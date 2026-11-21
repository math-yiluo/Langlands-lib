# Joint continuity after division by a holomorphic factor

`Langlands.Analysis.SeveralComplex.continuousOn_of_differentiableOn_of_mul`
uses a complex normed space `E`, a topological space `Y`, and an open
preconnected set `U ⊆ E`. Suppose `d : E → ℂ` is holomorphic and not
identically zero on `U`. Let `h : E → Y → ℂ` be holomorphic in `s ∈ U` for
each `y`. If `(s,y) ↦ d(s) h(s,y)` is continuous on `U × Y`, then so is
`(s,y) ↦ h(s,y)`. There is no differentiability assumption in `Y` and no
finite-dimensional assumption on `E`.

## Implemented proof

Where `d(s) ≠ 0`, use ordinary division of continuous functions. At an
arbitrary `s₀ ∈ U`, pick `w` near `s₀` with `d(w) ≠ 0` by holomorphic
uniqueness on `U`. The function `z ↦ d(s₀ + z • (w - s₀))` is holomorphic
on a disc of radius greater than one and nonzero at `1`. Isolated zeros
therefore give a small positive radius `r` whose circle avoids the zeros.
The whole affine closed disc lies in `U`.

For `(s,y)` near `(s₀,y₀)`, compactness of the closed disc keeps the
translated disc in `U`. On the boundary of the original disc there is joint
continuity by the nonzero-denominator case. Compactness of the circle makes
the bound on `|h(s + z • (w - s₀),y) - h(s₀ + z • (w - s₀),y₀)|` uniform
for `|z| = r` as `(s,y)` approaches `(s₀,y₀)`. Apply Mathlib's zeroth Cauchy
estimate in `z` to the difference of the two holomorphic slices; the same
bound holds at `z = 0`, giving continuity at the original point.

## Provenance

This is an internal consequence of the Library's nonvanishing-on-open-sets
lemma (`Meromorphic.exists_ne_zero_of_differentiableOn`), Mathlib's
one-variable isolated zeros and Cauchy estimate
(`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`), and the
compact tube lemma. The uniform-growth joint evaluation module uses it to
pass from a jointly continuous product to its pointwise holomorphic factor.
The lemma does not construct that factor or the holomorphic denominator.
