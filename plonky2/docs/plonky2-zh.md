<style>
h1 {
    border-bottom: none; 
}

h2 {
    border-bottom: none;
}
</style>


# <p align="center"> Plonky2: 使用 PLONK 和 FRI 的快速递归论证 </p>

<p style="text-align: center;"> Polygon Zero Team </p>

<p style="text-align: center;"> Draft </p>

<p style="text-align: center;"> September 7, 2022 </p>



## <p align="center"> Abstract </p> 

我们引入 Plonky2, 一种侧重于快速递归组合的密码学论证实现. 在普通笔记本电脑上, Plonky2 生成递归证明大约需要 300ms. 

Plonky2 的算术化基于 TurboPLONK, 但它用基于 FRI 的方案取代了 PLONK 的多项式测试方案. 由于 FRI 不需要大特征域, 
我们将见证编码在一个 64 位的域中, 这大大提高了证明者的性能. 

我们还演示了使用递归是如何将任意大的证明缩小到固定大小的. 根据所需的安全性和延迟, Plonky2 可以将任何证明缩小到大约 43 KB. 

## 目录
- [1. Introduction](#1-introduction)
- [2. Field selection](#2-field-selection)
- [3. Plonk modifications](#3-plonk-modifications)
- [4. Hashing](#4-hashing)
- [5. Polynomial testing](#5-polynomial-testing)
- [6. Optimizations](#6-optimizations)
- [7. Final protocol](#7-final-protocol)
- [8. evaluation](#8-evaluation)
- [References](#references)


## 1 Introduction

虽然证明组合的概念可以追溯到 PCP 文献 [1], 但实现实际的递归一直是一个重大挑战. 递归组合首先在实践中通过循环椭圆曲线得以实现 [2]. 虽然这是一个重要的里程碑, 但大型 MNT 曲线的使用限制了其实用性. 

最近 Halo [3] 展示了如何在不使用配对的情况下实现递归, 从而能够使用更小的椭圆曲线. 后续的工作, 如 Nova [4] 使用基于 Halo 的累积策略, 减少了某些增量验证的成本. 

像 Halo 这样的方案面临的一个挑战是, 尽管验证证明的大部分工作涉及该证明的基础域, 但约束必须在其标量域中进行计算. 由于这不是验证电路的本地域, 这些检查通常会被推迟到递归链中的下一个证明中进行. 然而, 这种推迟策略依赖于公共输入, 而验证公共输入本身需要使用一些非本地算术. 

为了避免与循环椭圆曲线相关的困难, 我们转向支持具有平滑子群的任意素数域的 FRI [5]. 尽管 Fractal [6] 以前展示了基于 FRI 的递归, 但其递归阈值是 $2^{21}$ R1CS 约束, 导致证明时间在分钟级. 

我们使用 PLONK [7] 算术化实现了更小的 $2^{12}$ 门的递归阈值, 并使用自定义门来针对验证者的瓶颈问题. 我们还使用了较小的域, 从而显著加快了证明时间. 

## 2 Field selection

我们把见证数据编码到素数域 $\mathbb{F}_{p}$, 这里 $p=2^{64} - 2^{32} + 1$. 该域是为了计算速度而选择的: 其元素在 64 位以内, 并且 $p$ 的结构产生了一种高效的约简方法. 

要理解为什么模 $p$ 的约简特别高效, 可以注意到
$$2^{64} \equiv 2^{32} - 1 \pmod{p}$$
因此 
$$
\begin{align*}
2^{96} &\equiv 2^{32}(2^{32} - 1) \pmod{p} \\
 &\equiv 2^{64} - 2^{32} \pmod{p} \\
 &\equiv -1 \pmod{p}.
\end{align*}
$$

为了简化一个128位的数字 $n$, 我们首先将 $n$ 重写为 $n_0 + 2^{64}n_1 + 2^{96}n_2$, 这里 $n_0$ 是64位, $n_1 , n_2 $ 为32位. 然后有
$$
\begin{align*}
n &\equiv n_0 + 2^{64}n_1 + 2^{96}n_2 \pmod{p} \\
  &\equiv n_0 + (2^{32} - 1)n_1 - n_2 \pmod{p}.
\end{align*}
$$

为了在计算机中执行此过程, 我们首先计算 $(2^{32} - 1)n_1$, 这可以通过位移和减法来完成. 然后我们将前两项模 $2^{64}$ 加, 如果发生溢出则减去 $p$. 接着我们模 $2^{64}$ 减去 $n_2$, 如果发生溢出则加上 $p$. 此时我们已将 $n$ 简化为一个64位整数. 这种部分约简对于大多数情况下已经足够, 这里可以通过最终的条件减法获得规范形式. 

我们选择的 $p$ 也减少了在寄存器中保留常量的需求. 特别地, 溢出加法需要我们减去 $p$ 来修正结果. 在64位算术中, 减去 $p$ 等价于加上 $2^{64} - p = 2^{32} - 1$. 方便的是, 许多架构都有根据进位标志将寄存器设置为 $0$ 或 $2^{32} - 1$ 的指令. 例如, x86有SBB指令, ARM64有CSETM指令. 因此, 尽管 $p$ 在约简算法中作为一个常量出现, 但它不需要保留在寄存器中, 这减少了寄存器压力和加载常量的开销. 

### 2.1 Extension field

在我们协议的某些部分, 为了保证正确性, 需要使用更大的域. 按照 [8] 中的方法, 我们在这种情况下使用扩展域 $\mathbb{F}_p(\phi) $, 具体来说是 $\mathbb{F}_p[X]/(X^2 - 7) $. 


## 3 PLONK modifications

### 3.1 Custom gates

根据像 TurboPLONK [9] 这样的先前工作, Plonky2 广泛使用自定义门. 为了说明这个模型, 假设我们正在设计一个用于(域)除法的门, 即 $q = x/y$, 或者等价地, $(qy = x) \land (y \neq 0)$. 为了确保 $y \neq 0$, 我们要求证明者提供一个假定的逆元 $i = 1/y$. 然后, 我们强制执行以下约束条件: 
$$
\begin{align*}
qy &= x, \\
yi &= 1.
\end{align*}
$$

更具体地说, 我们会将这些变量映射到线多项式上. 如果我们选择 $w_1(x), \ldots, w_4(x)$ 分别表示 $x, y, q, i$, 那么在重新排列后, 我们的约束条件可以写成: 
$$
\begin{align*}
w_3(x) w_2(x) - w_1(x) &= 0, \\
w_2(x) w_4(x) - 1 &= 0.
\end{align*}
$$

注意, 这些约束应仅在与除法门对应的轨迹行上强制执行. 一个简单的解决方案是预处理一个多项式 $d(x)$, 定义为: 

$$
d(g^i) = 
\begin{cases} 
1 & \text{如果第 } i \text{ 个门是除法门}, \\
0 & \text{否则}.
\end{cases}
$$

并使用 $d(x)$ 来"过滤"我们的除法约束: 
$$
\begin{align*}
d(x) \left( w_3(x) w_2(x) - w_1(x) \right) &= 0, \\
d(x) \left( w_2(x) w_4(x) - 1 \right) &= 0.
\end{align*}
$$


#### 3.1.1 Filtering constraints

如果我们有 $k$ 个自定义门, 引入 $k$ 个这样的过滤多项式会显著增加我们的多项式打开协议的成本. 如果我们将多个过滤多项式一起批处理, 可以用更少的多项式实现相同的效果. 这种技术受到 [10] 的启发. 

为了说明这种技术, 假设我们的电路使用了 $n$ 个自定义门并且固定一个标准顺序. 设 $f(x)$ 是一个多项式, 通过以下方式在 $\langle g \rangle$ 进行来定义: 
$$
f(g^i) = j  \text{如果第 } j \text{ 个门在第 } i \text{ 行被使用}
$$

然后第 $j$ 个门的约束可以通过以下表达式进行过滤: 

$$ f_j(x) = \prod_{\substack{k=0 \\ k \neq j}}^{n-1} (f(x) - k), $$

这个表达式在 $g^i$ 上非零当且仅当第 $j$ 个门在第 $i$ 行中被使用. 

注意, $f_j(x)$ 的次数为 $n-1$, 因此通过该多项式进行过滤可能会导致某些门的次数变得非常大. 这个问题可以通过将门划分为不同的子集, 并为每个子集定义不同的过滤多项式来轻松解决. 

### 3.2 Advice wires

某些轨迹元素不需要连接到任何其他轨迹元素. 例如, 我们通常会分配一列逆元素来实现非确定性的除法操作. 我们将这些称为建议线, 并将它们排除在 PLONK 的置换参数之外. 

这样做减少了我们协议中的 $\sigma_i$ 多项式的数量, 从而降低了置换参数的次数. 由于需要打开更少的多项式, 这也减少了证明的大小以及节省了验证者的工作. 

### 3.3 Cumulative products

假设我们的电路有 $r$ 条路由线. PLONK 的置换参数施加了 $r + 1$ 次数的约束: 

$$ Z(x) \prod_{i=1}^r f'_i(x) = Z(gx) \prod_{i=1}^r g'_i(x).$$

在我们的情况下, $r$ 很大, 这样的高次数约束显然是不理想的. 

我们可以将上述约束重写为: 
$$ Z(gx) = Z(x) \prod_{i=1}^r \frac{f'_i(x)}{g'_i(x)}.$$

为了获得低次约束, 我们将上面的积分成8项的块, 并引入一个证明者多项式 $\pi_i(x)$ 来保存每个累积乘. 令 $s = \lfloor r/8 \rfloor$, 然后我们有: 

$$
\begin{align*}
& \pi_1(x) = Z(x) \prod_{i=1}^8 \frac{f'_i(x)}{g'_i(x)}  \\

& \pi_2(x) = \pi_1(x) \prod_{i=9}^{16} \frac{f'_i(x)}{g'_i(x)}  \\

& \begin{align*}   \vdots \end{align*} \\

& Z(gx) = \pi_s(x) \prod_{i=8s+1}^r \frac{f'_i(x)}{g'_i(x)}. \\

\end{align*}
$$

这些方程适用于推导每个 $ x \in H $ 处的 $ \pi_i(x) $ 和 $ Z(gx) $ 的值, 但它们不能直接用作多项式约束, 因为它们包含的有理函数不一定是多项式. 为了获得多项式约束, 我们通过每个 $ g'_i(x) $ 项相乘, 得到类似于以下的约束：

$$ \pi_1(x) \prod_{i=1}^{8} g'_i(x) = Z(x) \prod_{i=1}^{8} f'_i(x) $$

对于其他累积乘积亦是如此. 

### 3.4 Soundness analysis

PLONK 论文 [7] 假设一个大的域, 因此任何与域大小成反比的 soundness 错误都被认为是可以忽略的. 由于我们的域大小远小于我们的安全目标, 我们必须进行更详细的分析, 并修改协议的部分内容以提升 soundness. 

#### 3.4.1 Permutation argument

我们对 PLONK 的置换论证进行直接分析. 假设 $ g \neq \sigma(f) $, 因此存在某个 $ j $ 使得 $ g(g_j) \neq f(g^{\sigma(j)}) $. 我们希望限定下面的可能性, 即对于随机的 $ \beta, \gamma \in \mathbb{F}_p^2 $, 有

$$ \sum_{i=1}^{n} (f(g^i) + \beta i + \gamma) = \sum_{i=1}^{n} (g(g^i) + \beta {\sigma(i)} + \gamma). $$

我们可以将两边视为关于 $ \beta $ 和 $ \gamma $ 分解的多项式. 考虑左边多项式中对应 $ i = \sigma(j) $ 的因子, 称为

$$ f(g^{\sigma(j)}) + \beta {\sigma(j)} + \gamma. $$

如果右边多项式包含相同的因子, 那么它必须以 $ \sigma(j) $ 作为 $ \beta $ 的系数, 因此它必须是与 $ i = j $ 相关的因子, 称为

$$ g(g^j) + \beta {\sigma(j)} + \gamma. $$

但由于 $ g(g^j) \neq f(g^{\sigma(j)}) $, 因此这些因子实际上并不相等, 因此多项式也不相等. 由于它们的总次数为 $ n $, Schwartz-Zippel 引理表明我们的约束条件在上述因子不相等的情况下满足的概率最多为 $ \frac{n}{|\mathbb{F}_p|} $. 

#### 3.4.2 Combining constraints

像许多 IOP(Interactive Oracle Proofs) 一样, PLONK 使用随机性将一组约束 $ c_0, \ldots, c_{l-1} $ 合并为单个约束. 特别地, 验证者选择一个随机数 $ \alpha \in \mathbb{F}_p $, 合并约束为
$$ C(x) = \sum_{i=0}^{l-1} \alpha^i c_i(x). $$

假设某些约束未满足: 对于某些 $ j, k $, 有 $ c_j(g^k) \neq 0 $. 我们希望证明, $ C(g^k) \neq 0 $ 有很高的概率. 考虑多项式
$$ p(\alpha) = \prod_{i=0}^{l-1} \alpha^i c_i(g^k). $$

由于与 $ \alpha^j $ 相关的 $ p(\alpha) $ 的系数非零, $ p(\alpha) $ 不是零多项式. 根据 Schwartz-Zippel 引理, 它最多有 $ l $ 个根. 因此, $ C(g^k) \neq 0 $ 的概率至多为 $ \frac{l}{|\mathbb{F}_p|} $. 

#### 3.4.3 Boosting soundness

上述提到的 soundness 错误对于实际应用来说过大. 为了增强子协议的 soundness, 我们简单地并行重复 $ r $ 次. 根据 tight
parallel repetition theorem, soundness 错误为 $ \epsilon^r $, 其中 $ \epsilon $ 是原始子协议的 soundness 错误. 

例如, 将置换论证重复三次会导致声音性错误为 $ \left( \frac{n}{|\mathbb{F}_p|} \right)^3 $. 对于任何 $ n \leq 2^{21} $, 这个 soundness 错误小于 $ 2^{-128} $. 

### 3.5 Public inputs

在Plonky2中, 任何可路由的轨迹元素都可以标记为公共输入. 电路本身对这些公共元素进行哈希处理, 并将哈希输出 $ h = (h1, \ldots, h4) $ 路由到一个 PublicInputGate. 这个 PublicInputGate 简单地施加以下约束: 

$$
\begin{align*}
  & w_1(x) = h_1, \\
  & w_2(x) = h_2, \\
  & w_3(x) = h_3, \\
  & w_4(x) = h_4. \\
\end{align*}
$$

相比之下, 在原始的 PLONK 协议中的约束系统涉及 $ PI(x) $, 这是通过插值 $l$ 个公共输入值的得到的多项式. 由于哈希允许我们将 $l$ "压缩"到 4 个, 我们可以将公共输入数据编码为约束系统中的四个常数, 而不是定义多项式来编码任意数量的公共输入数据. 

### 3.6 Zero-knowledge

PLONK 通过向轨迹多项式和置换多项式 $ Z(x) $ 添加随机倍数的 $ ZH(x) $ 来实现零知识. 这使得这些多项式的度数略高于二的幂, 这在我们的设置中是不可取的, 因为 FFT 和 FRI 算法处理的是定义在平滑乘法子群上的多项式. 

相反, 我们在填充到二的幂之前对证明多项式进行盲化. 为了对轨迹多项式进行盲化, 我们向轨迹中添加了填充有随机元素的行. 为了对 $Z(x)$ 进行盲化, 我们向轨迹中添加了成对的随机化行, 每对的列之间有复制约束. 我们参考 [11] 来获取更多详细信息和统计零知识证明. 请注意, 当使用 FRI 而不是 PCS 时, 必须调整更多的盲化因子. 

然后我们使用标准技术将 FRI 协议变成零知识: 

1. 因为发送在 $H$ 上的证明多项式的值会直接泄露见证信息, 我们改为在 $H$ 的陪集上发送评估. 

2. 如 [12] 中建议的那样, 我们通过将每个叶子包装在基于哈希的承诺中, 将 Merkle 树转换为隐藏的向量承诺. 

## 4 Hashing

在大多数基于 FRI 的证明实现中, 哈希计算是证明者和验证者的主要瓶颈. 由于生成递归证明的成本取决于证明成本和验证成本, 因此基于 FRI 的递归效率高度依赖于我们选择的哈希函数.  

为此, 我们决定在海绵结构中使用 $\text{Poseidon}^{\pi}$ [13]. 我们使用了12个$\mathbb{F}_p$ 元素的宽度, 并将 $x^7$ 作为 $S$ 盒. 为了达到128比特的安全性并保持推荐的安全边界, 我们使用了8个完整轮和22个部分轮, 总共使用了118个S盒.  

Plonky2 也支持 $\text{GMiMC}_{\text{erf}}$ [14]. 尽管它更高效, 但出于安全考虑, 我们在实践中应避免使用它. 

### 4.1 Hashing in the circuit 

在 Plonky2 中, 大约 $75\%$ 的递归电路被用于验证 Merkle 证明. 因此为了获得一个小型的递归电路, 高效地进行哈希计算是至关重要的. 

在大多数其他 SNARK 实现中, 对算术哈希的单次计算涉及跨行轨迹. 例如, Rescue 的计算中每轮可能会使用某一行. 轮常数可以通过预处理的多项式传递进来, 或者使用像周期列[8]这样的技术. 请注意, 这两种选项都有一些缺点 $-$ 更多的预处理多项式意味着更多的打开操作, 而周期列对行的放置施加了对齐要求. 

相比之下, Plonky2 使用单个 PoseidonGate 来计算整个 $\text{Poseidon}^{\pi}$ 的实例. 这种方法允许我们在约束系统中指定轮常数. 为了保持我们的约束低次数, 我们为每个 S 盒输入引入了"中间值"线, 导致约束为7次. 

这种设计确实导致了较宽的轨迹. Plonky2 使用了135列. 在更窄但更长的轨迹与更宽但更短的轨迹之间存在一些权衡, 我们发现这个宽度对于最小化证明大小和 FRI 验证成本是一个合理的平衡. 

## 5 polynomial testing 

低次数测试如 FRI 可以用来构建多项式承诺方案. 为了承诺于一个多项式 $p(x)$, 证明者简单地发送一个向量承诺到 $p(x)$ 的低度扩展. 为了打开 $p(x_0) = y_0$, FRI 协议在 $(p(x) - y_0)/(x - x_0)$ 上运行, 这是一个多项式, 当且仅当 $p(x_0) = y_0$. 然而, 这个构造假设 FRI 使用在解码半径 $(1 - \rho)/2$ 内的参数 $\delta$. 为了有效递归, 我们需要一个更大的 $\delta$. 这种情况下, 证明者不被限制于单个多项式. 尽管如此, 在发送到 $u \in \mathbb{F}^n_p$ 的向量承诺之后, 证明者被限制于在以 $u$ 为中心, $\delta$ 为半径为的汉明球中的多项式集合中. 

我们随后可以论证, 如果没有多项式满足我们的约束条件, 那么在随机选择的 $\zeta$ 处, 不太可能有这个汉明球中的任何多项式满足检查. 关于 soundness 分析, 我们参考 DEEP-ALI 协议 [15]. 虽然原始的 DEEP-ALI 分析假设了单一的见证多项式, 但在 [16] 和 [17] 中进行了进一步的泛化. 


## 6 Optimizations

### 6.1 Structure of the trace 

一个很自然的想法是将轨迹视为一个矩阵 $\mathbb{F}^{r \times c}$, 其中每一行对应一个门的导线. 然而, PLONK 的复制约束意味着某些轨迹元素将始终具有相同的值. 这些约束诱导出轨迹元素的一个划分, 其中两个元素属于同一集合, 当且仅当在布线图中它们之间存在路径. 

考虑到这一点, 另一个自然的结构是并查集森林. 在构建电路时, 我们从每个轨迹元素的单例集开始. 当两个元素之间添加复制约束时, 我们执行一个联合操作. 

随后在生成轨迹值时, 我们仅为每个代表元存储一个值, 而不是为每个轨迹单元格存储一个值. 这样做的好处是, 当填充一个值时, 无需将其复制到布线图中的相邻单元格中. 


### 6.2 FRI optimizations

虽然这些技术并不新颖, 但我们仍对 FRI 协议做了一些优化: 

1. 我们使用最少的 Merkle 树来构建协议. 例如, 我们将所有预处理的多项式(如 PLONK 的 $\sigma_i$ 和选择多项式)合并到一个单独的 Merkle 树中. 

2. 在优化证明大小时, 我们进行了全面搜索, 寻找一系列 FRI reduction arities 来最小化证明大小. 有时在早期的 FRI 轮中会使用较高的 arities, 而在后续轮中会使用较低的 arities. 在优化递归成本时, 我们使用固定的 arity 8, 以使验证者的工作更加均匀. 

3. 在任何需要一起查询连续区块的 Oracle 数据的地方, 我们将整个区块放置在 Merkle 树的一个叶子节点中. 例如, 在 FRI commit 阶段的 Merkle 树中, 一个叶子节点包含整个陪集上的评估值, 而不仅仅是单个点的评估值. 

4. 我们修剪重叠的 Merkle 路径来优化证明大小. 当同一 FRI 层中出现相同的查询索引时, 我们完全省略后续的响应. 

5. 在递归设置中, 我们不希望修剪创建出变长的 Merkle 路径. 相反, 我们让证明者发送 "Merkle caps" [18] 来替代 Merkle 根. 这使我们可以从每个 Merkle 路径中修剪一些哈希, 同时仍保持路径长度固定. 

6. 在 FRI 的原始描述中, 会一直执行约简直到最终的 codeword 变成 1 阶. 在实践中, 一旦达到一定的合理小度数, 我们就终止约简协议, 并由证明者发送这个约简后的多项式, 而不是一个常数. 

7. 参照[8], 我们使用 grinding 来增强安全性. 

这里的 arity 是 指 FRI 的一些参数. 


### 6.3 Poseidon

在 MDS 层中, 我们使用循环 MDS 矩阵, 其第一行为 [1, 1, 2, 1, 8, 32, 2, 256, 4096, 8, 65536, 1024]. 这种 MDS 矩阵可以实现多种优化. 首先, MDS 矩阵由二的幂组成. 这使得可以避免使用乘法, 使用在大多数硬件上更快的移位操作. 此外, 矩阵的阶相对较低. 在输入范围为 $0$ 到 $2^{64} - 1$ 的情况下进行整数矩阵乘法, 总是产生小于 $2^{81}$ 的向量阶. 这个界限简化了最终的约简过程. 

除了这两个属性外, 我们在 x86-64 和 ARM64 的实现中通过大量使用 SIMD (单指令多数据流)操作和手动调优的汇编语言来加速哈希计算. 循环属性简化了 SIMD 实现 $-$ 通过在每一步适当地排列输入向量, 我们可以确保所有条目都乘以相同的常数. 这使我们能够使用向量乘以标量或立即数的指令, 从而减少寄存器压力. 

## 7 Final protocol

这里我们描述 Plonky2 协议的交互式变体. 非交互式变体通过 Fiat-Shamir 变换获得. 

设 r 是我们的重复参数. 这是我们重复执行某些检查的次数, 特别是那些具有 soundness 错误 $y/|\mathbb{Fp}|$ 的检查, 其中 $y$ 是某个"小"量, 比如我们的电路度数或约束个数. 

我们使用 $\text{Com}(\vec{p})$ 表示对多项式向量的承诺. 具体来说, 它代表了一个 Merkle Cap, 其中每个叶子对应点 $x \in H$, 并包含值 $p_1(x), \ldots, p_k(x)$. 



### 7.1 Preprocessing

1. **P**, **V** 构建电路并计算 $\vec{C}$, 一组编码了每个门配置的常数的多项式, 以及编码了在文献[7]中描述的"扩展"置换的 $\vec{\sigma}$. 

2. **P**, **V** 构建包含 $\vec{C}$ 和 $\vec{\sigma}$ 的 Merkle 树. 

3. **P** 将这棵 Merkle 树存储为其证明密钥. 

4. **V** 将 $\text{Com}(\vec{C}, \vec{\sigma})$ 存储为其验证密钥. 

### 7.2 Main protocol 

1. **P** 生成见证 $\vec{w}$, 并发送 $\text{Com}(\vec{w})$, 即每个线多项式 $w(x)$ 的承诺. 

2. **V** 随机生成 $\beta_{1}, \ldots, \beta_{r}, \gamma_{1}, \ldots, \gamma_{r} \in \mathbb{F}_{p}$, 这些是我们置换参数中使用的随机数. 

3. **P** 发送 $\text{Com}(\vec{Z}, \vec{\pi})$, 即每个置换多项式 $Z(x)$ 和部分乘积多项式 $\pi(x)$ 的承诺. 

4. **V** 随机生成 $\alpha_{1}, \ldots, \alpha_{r} \in \mathbb{F}_{p}$, 这些是用于组合约束的随机数. 

5. **P** 发送 发送 $\text{Com}(\vec{q})$, 即每个商多项式 $q(x)$ 的承诺. 特别地, $q_{i}(x) = C_{i}(x)/Z_{H}(x)$, 其中 $C_{i}(x)$ 是已使用 $\alpha_{i}$ 的幂约简的组合约束(参见第 3.4.2 节), $Z_{H}(x) = x^{n} − 1$ 是在 $H$ 上为零的多项式. 

6. **V** 随机生成 $\zeta \in \mathbb{F}_{p}(\phi)$, 这是我们要测试多项式恒等式使用的随机数. 

7. **P** 发送 $\vec{P}(\zeta)$, 即每个多项式在 $\zeta$ 处的值, 这里 $\vec{P}$ 是所有上述多项式的组合: $\vec{P}=(\vec{C}, \vec{\sigma}, \vec{w}, \vec{Z}, \vec{\pi}, \vec{q})$. 

8. 为验证这些多项式的打开, **P**, **V** 参与以下所述批量打开 FRI 协议: 
$$
\begin{align*}
\vec{B} = \bigg ( \frac{p_{i}(x) - p_{i}(\zeta)}{x - \zeta} \bigg | p_{i} \in \vec{P} \bigg ).
\end{align*}
$$

9. **V** 使用 $\vec{P}$ 推断我们组合约束多项式的值 $c_{1}(\zeta), \ldots, c_{r}(\zeta)$, 并声明每个 $c_{i}(\zeta) = q_{i}(x) Z_{H}(x) $. 

### 7.3 FRI protocol 

我们的 FRI 协议与文献 [15] 中描述的几乎完全相同, 但有一些小差异, 例如我们使用 Merkle caps 替代 Merkle 根. 

1. **V** 随机生成 $\alpha \in \mathbb{F}(\phi)$, 这是用于将批量 $Bs$ 约简为单个 codeword 的随机数. 

2. **P** 发送 $\text{Com}(h_{0})$, 其中 $h_{0}(x)$ 是深度组合多项式, 
$$ h_{0}(x) = \sum_{i=0}^{|\vec{B}|-1} \alpha_{i} \vec{B}_{i}(x)  .$$

3. **P**, **V** 执行 FRI 的承诺阶段. 对于每个约简 arity $l_{i}$,  

   (a) **V** 随机生成 $\beta \in \mathbb{F}(\phi)$. 

   (b) **P** 将 $h_{i}(x)$ 重写为
   $$ h_{i}(x) = \sum_{j=0}^{l_{i} - 1} x^{j} h_{i,j}(x^{l_{i}}) ,$$

   其中每个 $h_{i, j} 包含 $h_{i}(x)$ 的系数, 其指数与 $j$ 模 $l_{i}$ 同余. 然后 **P** 发送 $\text{Com}(h_{i+1})$, 即多项式 $h_{i+1}(x)$ 的承诺,  
   $$ h_{i+1}(x) = \sum_{j = 0}^{l_{i} - 1} \beta^{j} h_{i,j}(x) .$$ 
   
4. **V** 随机生成 $\tau \in \mathbb{F}_{p}^{4}$. 

5. **P** 执行"grinding" [15] 并发送他们工作证明的见证 $\mu$. 

6. **V** 断言 $H(\tau, \mu)$ 的二进制编码中至少包含 proof_of_work_bits 个前导零. 

7. **V** 随机生成 num_query_rounds 个随机索引 $q_{1}, \ldots, q_{k} \in \{ 0, \ldots, n-1\}$.

8. 对于每个查询索引 $q_{i}$, 

   (a) **P** 发送值 $\vec{P}(x)$ 和每个 $h_{i}(x)$, 其中 $x$ 是定义 codeword 的陪集中的第 $i$ 个点. 

   (b) **V** 在 $x$ 处执行一系列一致性检查. 首先是在 $\vec{P}(x)$ 和 $h_{0}(x)$ 之间, 然后是在每对 $(h_{i}(x), h_{i+1}(x))$ 之间. 具体细节可参考文献 [8]. 


## 8 Evaluation

Plonky2 的递归阈值取决于各种设置. 在优化证明者速度时, 我们通常使用 $1/8$ 的 codeword 率. 然后, 当配置为具有100位 conjectured 安全性时, Plonky2 的阈值为 $2^12$ 个门. 这些递归证明在2021年款 Macbook Air 上大约需要 300 ms 来生成. 

在优化尺寸时, 我们使用更大的 codeword 率. 使用 $1/256$ 的 codeword 率时, Plonky2 能够将任何证明压缩到大约 43 KB. 这些证明大约需要 11.6 s 生成, 同样是在2021年款Macbook Air 上. 

## References

[1] S. Arora and S. Safra, “Probabilistic checking of proofs: A new characterization of NP,” Journal of the ACM (JACM), vol. 45, no. 1, pp. 70–122, 1998.

[2] E. Ben-Sasson, A. Chiesa, E. Tromer, and M. Virza, “Scalable zero knowledge
via cycles of elliptic curves.” Cryptology ePrint Archive, Report 2014/595,
2014. https://ia.cr/2014/595.

[3] S. Bowe, J. Grigg, and D. Hopwood, “Recursive proof composition without a
trusted setup.” Cryptology ePrint Archive, Report 2019/1021, 2019. https://ia.cr/2019/1021.

[4] A. Kothapalli, S. Setty, and I. Tzialla, “Nova: Recursive zero-knowledge arguments from folding schemes.” Cryptology ePrint Archive, Report 2021/370,
2021. https://ia.cr/2021/370.

[5] E. Ben-Sasson, I. Bentov, Y. Horesh, and M. Riabzev, “Fast Reed-Solomon
Interactive Oracle Proofs of Proximity,” in 45th International Colloquium on
Automata, Languages, and Programming (ICALP 2018), vol. 107 of Leibniz International Proceedings in Informatics (LIPIcs), pp. 14:1–14:17, Schloss
Dagstuhl–Leibniz-Zentrum fuer Informatik, 2018.

[6] A. Chiesa, D. Ojha, and N. Spooner, “Fractal: Post-quantum and transparent recursive proofs from holography.” Cryptology ePrint Archive, Report
2019/1076, 2019. https://ia.cr/2019/1076.

[7] A. Gabizon, Z. J. Williamson, and O. Ciobotaru, “PLONK: Permutations
over Lagrange-bases for oecumenical noninteractive arguments of knowledge.”
Cryptology ePrint Archive, Report 2019/953, 2019. https://ia.cr/2019/
953.

[8] StarkWare, “ethSTARK documentation.” Cryptology ePrint Archive, Report
2021/582, 2021. https://ia.cr/2021/582.

[9] A. Gabizon and Z. J. Williamson, “Proposal: The Turbo-PLONK program
syntax for specifying SNARK programs,” 2020. https://docs.zkproof.org/
pages/standards/accepted-workshop3/proposal-turbo_plonk.pdf.

[10] D. Hopwood, “Selector combining,” 2022. https://hackmd.io/@daira/SkjDVkLCd.

[11] D. Lubarov, “Adding zero knowledge to PLONK-Halo,” 2020. https://mirprotocol.org/blog/Adding-zero-knowledge-to-Plonk-Halo.

[12] E. Ben-Sasson, A. Chiesa, and N. Spooner, “Interactive oracle proofs.” Cryptology ePrint Archive, Report 2016/116, 2016. https://ia.cr/2016/116.

[13] L. Grassi, D. Khovratovich, C. Rechberger, A. Roy, and M. Schofnegger, “Poseidon: A new hash function for zero-knowledge proof systems.” Cryptology
ePrint Archive, Report 2019/458, 2019. https://ia.cr/2019/458.

[14] M. R. Albrecht, L. Grassi, L. Perrin, S. Ramacher, C. Rechberger, D. Rotaru,
A. Roy, and M. Schofnegger, “Feistel structures for MPC, and more.” Cryptology ePrint Archive, Report 2019/397, 2019. https://ia.cr/2019/397.

[15] E. Ben-Sasson, L. Goldberg, S. Kopparty, and S. Saraf, “DEEP-FRI: Sampling outside the box improves soundness.” Cryptology ePrint Archive, Report
2019/336, 2019. https://ia.cr/2019/336.

[16] A. Kattis, K. Panarin, and A. Vlasov, “RedShift: Transparent SNARKs
from list polynomial commitment IOPs.” Cryptology ePrint Archive, Report
2019/1400, 2019. https://ia.cr/2019/1400.

[17] E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, and S. Saraf, “Proximity
gaps for Reed-Solomon codes.” Cryptology ePrint Archive, Report 2020/654,
2020. https://ia.cr/2020/654.

[18] A. Chiesa and E. Yogev, “Subquadratic SNARGs in the random oracle
model.” Cryptology ePrint Archive, Report 2021/281, 2021. https://ia.cr/2021/281.
