# First-row unipotent matrices for the Jacquet–Shalika test vectors

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, formula (4), printed page 328).

- `firstRowNil z` is the matrix of `GL_(n+2)` with first row `(0, z_0, …, z_n)` and
  all other rows zero; it squares to zero. `firstRowUnipotent z = 1 + firstRowNil z` is
  the source's `n(u, v) = [[1, u, v], [0, 1, 0], [0, 0, I]]`, with `z = (u, v)`; its inverse
  is `1 - firstRowNil z` and `firstRowUnipotent_mul` gives `n(z) n(z') = n(z + z')`.
- `firstRowUnipotent_mem`: it is upper unipotent; `firstRowUnipotent_superdiagonal`: its
  first-superdiagonal sum is `z_0`, so the standard character takes the value `ψ(z_0)`.
- `mul_firstRowUnipotent`: if `M` has first column `e_0` then
  `M n(z) = n(z') M` with `z'_j = Σ_k z_k (M⁻¹)_(k+1, j+1)`. The proof uses that `M⁻¹`
  then also has first column `e_0`. Only the first column of `M` is needed.
- `whittaker_mul_firstRowUnipotent`: for a standard Whittaker function `W` and such `M`,
  `W(M n(z)) = ψ(Σ_k z_k (M⁻¹)_(k+1, 1)) W(M)`. With `M = diag(1, g)` this is
  `W(M) Φ̂(g⁻¹ e_1)`-type evaluation used for the dual side.
- `firstRowUnipotent_zero_apply` and `weylLong_mul_firstRowUnipotent_last`: the first row
  of `n(z)`, hence the last row of `w n(z)`, is `(1, z_0, …, z_n)`.
- `firstRowUnipotent_mem_levelSubgroup`: for integral `z`, `n(z)` lies in every level
  subgroup `Conductor.levelSubgroup F (n+1) f` (its last row is the last standard row).
