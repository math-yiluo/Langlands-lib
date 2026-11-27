# Special unitary matrices of a skew Gram matrix over coefficient algebras

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGalois` (namespace
`Langlands.GroupScheme.Quaternionic.SkewUnitary`).

Let `D` be a division algebra over a field `F`, `τ` an involution of the first kind of `D`,
and `H` an `n × n` matrix over `D`. For a commutative `F`-algebra `R`, matrices over
`R ⊗[F] D` carry the conjugate transpose `(τ.baseChange R).matrix (Fin n)`.

- `coeffMap f` applies `Algebra.TensorProduct.map f (AlgHom.id F D)` to every entry, for an
  `F`-algebra map `f : R →ₐ[F] S`; `coeffMap_comp`, `coeffMap_id` and `coeffMap_adjoint`
  (compatibility with the conjugate transpose) are proved.
- `gramOver n H R` is the image `1 ⊗ H` of `H` in matrices over `R ⊗[F] D`;
  `coeffMap_gramOver` says it is preserved by coefficient maps.
- `IsSU τ H M` is the proposition `M (1 ⊗ H) Mᵗ^τ = 1 ⊗ H ∧ matrixReducedNorm R M = 1`: `M` is
  an isometry of the form with Gram matrix `H` with reduced norm one. `suGroup τ H R` is the
  subgroup of units of `M_n(R ⊗ D)` satisfying it; these are the `R`-points of the special
  unitary group `SU(h)` of the form (the reduced norm of `M_n(R ⊗ D)` is
  `matrixReducedNorm`).
- `unitMap f` is `coeffMap f` on units; `unitMap_mem` shows that it preserves `suGroup`.
  Automorphisms of a coefficient field act on `suGroup` in this way.
