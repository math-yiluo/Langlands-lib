# Haar measure on compact open subgroups in additive coordinates

Module `Langlands.BaseChange.TwistedLocalDescent.HaarRestrict`.

- `restrict_eq_smul_map_normalizedHaar`: for a topological group `G` with Haar measure `μ` and a
  compact open subgroup `K`,
  `μ|_K = μ(K) • (normalizedHaar K).map (↑)`. The comap of `μ` to `K` is a finite left invariant
  measure, hence `μ(K)` times the normalized Haar measure (`haarMeasure_unique`).
- `map_val_restrict_congruenceBall`: over an ultrametric proper nontrivially normed field `𝕂`,
  for a compact congruence subgroup `U = {‖g − 1‖ ≤ r}` of `GL_n(𝕂)` (as in
  `exists_congruenceBall`; the hypothesis is that `g ↦ g − 1` maps `U` onto `B(0, r)`), a Haar
  measure `μG` and an additive Haar measure `ν` on `M_n(𝕂)`,
  `(μG|_U).map (g ↦ g) = μG(U) ν(B(1, r))⁻¹ • ν|_{B(1, r)}`. With the previous item this follows
  from the Library's `BaseChange.map_normalizedHaar_eq_restrict_of_units`, which identifies the
  normalized Haar measure of a compact group of units embedded openly in a ring with normalized
  additive Haar measure on its image.
