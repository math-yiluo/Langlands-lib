# Local isometries from coboundary data

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisLocal`.

For fields `F ⊆ K ⊆ M` with `M/K` finite Galois:

- `tensorIncl_injective`, `coeffMap_tower_injective`: `K ⊗[F] D → M ⊗[F] D` and its matrix
  version are injective.
- `exists_unitMap_eq_of_fixed`: a unit over `M ⊗ D` fixed by `Gal(M/K)` comes from a unit
  over `K ⊗ D` (both the matrix and its inverse descend).
- `coeffMap_restrictNormal`, `unitMap_restrictNormal`: for `L ⊆ M` normal over `F`, the
  action of `s ∈ Gal(M/K)` on images of matrices over `L ⊗ D` is the action of the
  restriction of `s` to `L`.
- `GramDescent.exists_isometry_of_coboundary`: if, over `M`, the extended values of `c` are the
  coboundary `b * s(b)⁻¹` of `b ∈ suGroup τ H M` for all `s ∈ Gal(M/K)`, then
  `T = b⁻¹ * p` is `Gal(M/K)`-fixed; its descent `t` over `K` satisfies
  `t (1 ⊗ H') t* = 1 ⊗ H`, where `H'` is the descended Gram matrix.
