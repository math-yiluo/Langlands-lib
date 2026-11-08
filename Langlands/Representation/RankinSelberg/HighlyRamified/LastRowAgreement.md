# Agreement of level-fixed functions off the mirabolic subgroup

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`, replacing the
matrix factorization (4.4.20)–(4.4.21) of Jacquet–Shalika 1985 (printed pages 330–331)
by a simpler one.

- `mem_levelSubgroup_of_entries`: an invertible matrix over the field whose entries and
  inverse entries are integral and whose last row is congruent to the last standard row
  modulo `𝔭^f` lies in the published `Conductor.levelSubgroup F n f`. The proof builds
  the integral invertible matrix from the two entrywise integral matrices.
- `lastRowNil c` is the matrix whose last row is `(c_0, …, c_(n-1), 0)` and whose other
  rows vanish; it squares to zero, so `lastRowUnipotent c = 1 + lastRowNil c` is
  invertible with inverse `1 - lastRowNil c`. It is the lower unipotent matrix
  `[[I, 0], [c, 1]]`. `lastRowUnipotent_mem_levelSubgroup`: if every `c_j` lies in
  `𝔭^f` it belongs to the level-`f` subgroup.
- `lastRow_mul_lastRowUnipotent_inv`: for `m` with last row `ℓ` and `ℓ_last ≠ 0`,
  `m · [[I,0],[ℓ/ℓ_last,1]]⁻¹ · ℓ_last⁻¹` has last row equal to the last standard row,
  i.e. lies in the mirabolic subgroup `P`.
- `eq_of_lastRow_congruence`: let `W₁, W₂` be functions on `GL_(n+1)(F)`, right invariant
  under `Conductor.levelSubgroup F n f`, with `W_i(z g) = ω(z) W_i(g)` for scalar `z`, and
  equal on `P`. If `m` has last row `ℓ` with `ℓ_last ≠ 0` and `ℓ_j/ℓ_last ∈ 𝔭^f` for
  `j ≠ last`, then `W₁(m) = W₂(m)`. Indeed `m = z p k` with `z = ℓ_last`, `p ∈ P` and
  `k = [[I,0],[ℓ/ℓ_last,1]]` in the level-`f` subgroup.

In the stability proof `m = diag(g,1) w_r n(u,x,y)` has last row `(1,u,x,y)`, so the
conditions are `y⁻¹, y⁻¹u, y⁻¹x ∈ 𝔭^f`; this gives the equality `I₁ = I₂` of JS85 §4.4.
