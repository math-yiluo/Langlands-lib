# Factorization integrals over right-invariant measurable sets

Author: Worker 306.

This derived, internal module extends the Tonelli argument in
`Langlands.Analysis.Local.CompactFactorizationIntegral`. It introduces
`RightSubgroupInvariant K C`, which means that membership in the set `C`
is unchanged by right multiplication by any element of the subgroup `K`.
The module does not require a topology or assert that a suitable set exists.

Suppose every element of the measurable group `G` factors as `ι x * k`
with `k ∈ K`. Let `μ` be an s-finite left-invariant measure on `G` and
`ρ` an s-finite measure on `X`. The measurable map `ι` must admit a
`ρ`-preserving reparametrization for left multiplication by `(ι x₀)⁻¹`,
for every `x₀`. For a measurable right-`K`-invariant set `C` and a
measurable nonnegative extended-real function `F`, the theorem
`lintegral_rightInvariant_lintegral_mul` proves

```text
∫ c ∈ C, ∫ x, F (ι x * c) dρ dμ
  = ρ {x | (ι x)⁻¹ ∈ C} * ∫ y, F y dμ.
```

The normalizing mass involves the inverse of `ι x`; the set `C` need
not be inversion invariant. No positivity or finiteness hypothesis is
needed for this identity.

The implemented proof uses Tonelli twice. Between these swaps it
translates the `C` integral by `ι x`, using left invariance of `μ`.
For a fixed `y = ι x₀ * k₀`, right invariance of `C` removes `k₀`
from the indicator condition. The measure-preserving reparametrization
then identifies the inner indicator integral with the constant mass
displayed above.

The corollary `lintegral_lt_top_of_rightInvariant_majorant` assumes
`μ C < ∞`, nonzero normalizing mass, and a single finite bound `B`
for the parameter integral at every `c ∈ C`. Monotonicity bounds the
double integral by `μ C * B`. The identity and the nonzero mass then
imply finiteness of the ambient integral.

The intended use is a measurable neighborhood invariant under a compact
factor in an Iwasawa decomposition. Its ambient measure may be positive
even when that compact subgroup has measure zero. This module supplies
only the abstract measure identity and finiteness implication, not an
adelic quotient formula or an analytic Mellin estimate.
