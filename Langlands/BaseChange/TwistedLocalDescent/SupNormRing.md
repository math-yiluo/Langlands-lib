# The sup-norm matrix ring and its congruence balls

Module `Langlands.BaseChange.TwistedLocalDescent.SupNormRing`. Over an ultrametric nontrivially
normed field `𝕂`:

- `matrixSupNormedRing`, `matrixSupNormedAlgebra`: the entrywise sup norm makes `M_n(𝕂)` a normed
  ring and a normed `𝕂`-algebra (submultiplicativity from `matrix_norm_mul_le`);
  `matrix_properSpace`: `M_n(𝕂)` is proper when `𝕂` is.
- `exists_congruenceBall`: for complete proper `𝕂` there is `r₀ > 0` such that for every
  `r ∈ (0, r₀]` the set `U = {g ∈ GL_n(𝕂) : ‖g − 1‖ ≤ r}` is a compact open subgroup and
  `g ↦ g − 1` maps it onto the closed ball of radius `r`. This is the Library's
  `Analysis.unitsCoordinateBall` for the identity chart of `M_n(𝕂)`.
