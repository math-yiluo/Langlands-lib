# Original compact integrals with a different source Levi compact

This derived internal module proves the analytic comparison needed when the
source Levi spherical function is formed with a compact subgroup different
from the original ambient compact intersection. It composes the abstract
Iwasawa weight identities, the compact lower bound in
`LeviCompactWeightComparison`, and Fubini on compact groups. It does not assert
a new original-literature statement.

The ambient data are a topological group `G`, an original compact open subgroup
`K`, a factorization `G = P₀ K`, and a positive character `δ₀` trivial on
`P₀ ∩ K`. `LeviData` supplies the larger parabolic `P`, its Levi `M`, the
projection, and compatible characters. Let `KM` be any compact open subgroup
of `M` with its displayed factorization `M = (P₀ ∩ M) KM`. The minimal Levi
character must be trivial on its intersection with `KM`, and the parabolic
character must be trivial on `KM`. The theorem retains these hypotheses
explicitly. No containment `KM ⊆ K`, or equality with `K ∩ M`, is assumed.

`integral_iwasawaWeight_mul_mul` proves, for arbitrary `a,g`,

`∫_K weight(a k g) dk = weight(a) Ξ(g)`.

Factor `a = q k'` with `q ∈ P₀`, use left `P₀` equivariance of the original
weight, and translate the compact Haar variable by `k'`. The factor order is
unchanged. This identity is the inner averaging step already used in the
published spherical product-formula proof.

`sourceLeviXiComparisonConstant` is the average of the original ambient weight
on `KM` divided by the fixed positive lower bound for that weight on `KM`.
Its positivity theorem follows from continuity and strict positivity of the
weight and the probability normalization of compact Haar measure. The
constant is fixed before all group points, coefficient sections and twists.

`arbitraryCompactLeviXiWeight` uses the original ambient factorization and
its actual chosen Levi component, but uses the spherical function of `M`
formed with `KM`. For every point,
`LeviData.arbitraryCompactLeviXiWeight_le_average` bounds this source weight
by the reciprocal lower constant times the `KM` average of the original
ambient weight. The proof writes the point as its original chosen parabolic
factor times a member of the original `K`, uses right `K` invariance, applies
the earlier pointwise weight comparison, then integrates over `KM`.

`LeviData.norm_compactIntegral_le_xi_arbitraryCompact` is the coefficient
integral comparison. Suppose the norm of a complex kernel is bounded by a
nonnegative constant `C` times this source weight. Then its integral over the
original `K` is bounded by

`C * sourceLeviXiComparisonConstant * Ξ(g)`,

where `Ξ` is the original ambient spherical function. The proof uses the
continuous majorant `weight(kM k g)` on `KM × K`. It is integrable on the
compact product. Fubini and the weight-averaging identity evaluate its double
integral as the `KM` average of `weight(kM)` times `Ξ(g)`. The norm bound for
the original complex integral follows by domination. Second countability of
`G` supplies the product Borel compatibility. No measurability of the
choice-dependent Levi component or of the original complex kernel is added
as a premise to the comparison.

The original ambient compact group, its normalized Haar measure and its
spherical function are preserved. This module does not yet discharge the
actual rational-point source compact and modulus hypotheses, prove a bound
for a particular representation, or prove the wave-packet Schwartz target.
