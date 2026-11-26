# Measurable averages along a compact radical quotient

The module works with the Library's normalized quotient Haar probability
on $U(F)\backslash U(\mathbb A_F)$ for a closed adelic subgroup with
compact rational quotient. The ambient discrete subgroup $\Lambda$
contains the rational points of $U$. For the rational invariance and
integration results, $\Lambda$ also normalizes both the adelic subgroup
and its rational lattice. These hypotheses apply to $U=N_P$ and
$\Lambda=P(F)$ in the truncation pairing.
[Normalized subgroup quotient measure](AdelicSubgroupHaarMeasure.md)

- `exists_compact_radical_representatives` lifts the compact radical
  quotient to a compact set of representatives $E$ in the subgroup.
  For a measurable, locally bounded and $\Lambda$-invariant function
  $f$, the bound for $f$ on $EC$ bounds all integrands $f(nx)$ for
  $x\in C$ compact, because $f(nx)$ depends only on the radical class
  of $n$. Joint measurability follows by descending $([n],x)\mapsto
  [nx]$ to $\Lambda\backslash G(\mathbb A_F)$ and composing with the
  measurable descent of $f$. The fibre probability then gives
  `integrable_radical_integrand` and `compactAverage_locallyBounded`.
  [Continuous quotient evaluation](CompactQuotientSubgroupAverage.md)
- `compactAverage_mul_left` conjugates the radical by a rational
  parabolic element to compare the averages at $\lambda x$ and $x$.
  The induced automorphism preserves the normalized quotient measure
  because it preserves the rational lattice. [Quotient automorphism invariance](AdelicConstantTermTransitivity.md)
- `setIntegral_compactAverage` uses a Borel fundamental domain for
  $\Lambda$ in the ambient group. Push forward the product of the
  restricted ambient Haar measure and the radical probability by
  $(x,[n])\mapsto[nx]$. On indicators of measurable subsets of the
  outer quotient, `ConstantTermAverage.setLIntegral_lowerConstantTerm`
  identifies this pushforward with the quotient of ambient Haar
  measure. For an integrable complex function on the outer quotient,
  this measure identity gives product integrability and permits Fubini.
  It yields preservation of the integral under the normalized average.
  [Nonnegative constant-term identity](AdelicConstantTermAverage.md)

These lemmas implement the normalized radical integration used to
exchange factors in Arthur 2005, Proposition 13.1(c), p. 69.
[Source details](ArthurTruncationSelfAdjointProof.md#sources)
