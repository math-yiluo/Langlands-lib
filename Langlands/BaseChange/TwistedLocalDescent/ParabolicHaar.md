# Haar measure of a standard block parabolic near the identity

Module `Langlands.BaseChange.TwistedLocalDescent.ParabolicHaar`.

- `parabolicSubalgebra B`: the block upper triangular matrices
  (`Matrix.blockTriangularSubalgebra` for the block of each coordinate);
  `mem_parabolic_iff_blockTriangular`: `g ∈ P` iff `g` is block upper triangular, so `P` is the
  unit group of this subalgebra (`parabolicToUnits`).
- `isClosed_parabolicSubalgebra`, `isClosed_parabolic_of_normed`, and the topological instances
  on the subalgebra (`parabolicSubalgebra_locallyCompact`,
  `parabolicSubalgebra_isTopologicalRing`, `matrix_locallyCompactSpace`).
- `map_val_restrict_parabolic_congruenceBall`: over an ultrametric, proper, nontrivially normed
  field, for a left Haar measure `μP` on `P`, an additive Haar measure `νS` on the subalgebra `S`
  and a compact congruence subgroup `U` of radius `r > 0`,
  `(μP|_{P ∩ U}).map (p ↦ p) = μP(P ∩ U) νS(R)⁻¹ • (νS|_R).map (↑)`, where `R ⊆ S` is the set of
  elements within `r` of `1`. The group `P ∩ U` is compact open in `P`, it maps homeomorphically
  onto the open set `R` of units of `S` (every `W ∈ S` with `‖W − 1‖ ≤ r` is the matrix of an
  element of `U`, which is block upper triangular), and the statement follows from
  `restrict_eq_smul_map_normalizedHaar` and `BaseChange.map_normalizedHaar_eq_restrict_of_units`.
