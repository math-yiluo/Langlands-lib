# Galois descent for coefficients in `M ⊗ D`

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisDescent`.

For fields `F ⊆ K ⊆ M` with `M/K` finite Galois and a finite-dimensional `F`-algebra `D`,
`tensorIncl` is the inclusion `K ⊗[F] D → M ⊗[F] D` and `tensorAut s` the action of
`s ∈ Gal(M/K)` on the first factor.

- `exists_tensorIncl_eq_of_fixed`: an element of `M ⊗[F] D` fixed by every `tensorAut s`
  is the image of an element of `K ⊗[F] D`. The proof chooses an `F`-basis of `D`, so that
  `M ⊗ D ≅ M^d` coordinatewise, and applies `IsGalois.mem_range_algebraMap_iff_fixed` to
  every coordinate.
- `exists_coeffMap_eq_of_fixed`: the same statement entrywise for matrices.
