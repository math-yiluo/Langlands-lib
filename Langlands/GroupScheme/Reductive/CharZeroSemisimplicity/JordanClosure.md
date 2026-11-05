# Jordan semisimple parts of tangent matrices

Author: Worker 1498.

This module is an internal helper for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`. It extends the
Library theorem `tangentMatrix_semisimpleKernel` from representations indexed by
`Fin n` to representations indexed by any finite type. It also shows that
Jordan semisimple parts of block-diagonal endomorphisms are computed blockwise.
The perfect field `k` supplies the canonical Jordan semisimple part
`Langlands.LinearAlgebra.jordanSemisimplePart`, defined in
`Langlands.LinearAlgebra.JordanChevalleyFunctoriality`.

## Declarations

- `Langlands.LinearAlgebra.jordanSemisimplePart_prodMap`: for finite-dimensional
  `V`, `W` over a perfect field and `f : End V`, `g : End W`,
  `jordanSemisimplePart (f.prodMap g) =
    (jordanSemisimplePart f).prodMap (jordanSemisimplePart g)`.
- `toLin'_reindex_comp_funLeft`: for `e : n ≃ m`, the linear map of the
  reindexed matrix `Matrix.reindex e e M` composed with `funLeft e.symm` equals
  `funLeft e.symm` composed with the linear map of `M`.
- `toLin'_tangentMatrix_semisimpleKernel` ([PerfectField k],
  [IsAffineHom G.X.hom]): for every `ρ : MatrixRepresentation G n` with `n` a
  finite type and every `X ∈ lieKernel G k`,
  `toLin' (ρ.tangentMatrix k (semisimpleKernel G X)) =
    jordanSemisimplePart (toLin' (ρ.tangentMatrix k X))`.
  Here `semisimpleKernel G X` is the Library's semisimple component of `X`,
  defined through the Jordan decomposition of the translation derivation.

## Proofs

`jordanSemisimplePart_prodMap`: the inclusions `inl : V → V × W` and
`inr : W → V × W` intertwine `f`, respectively `g`, with `f.prodMap g`. The
Library theorem `jordanSemisimplePart_intertwines` says that intertwiners carry
the semisimple part of the source to the semisimple part of the target. Hence the
semisimple part of `f.prodMap g` agrees with `(jordanSemisimplePart f).prodMap
(jordanSemisimplePart g)` on `inl` and on `inr`, and so they are equal
(`LinearMap.prod_ext`).

`toLin'_reindex_comp_funLeft` is `Matrix.submatrix_mulVec_equiv`.

`toLin'_tangentMatrix_semisimpleKernel`: let `e : n ≃ Fin (card n)` and let
`ρ₀` be the reindexed representation `Chevalley.reindexRepresentation e ρ`. Its
tangent matrices are the reindexed tangent matrices (`tangentMatrix_reindex`),
and the Library theorem applies to `ρ₀`. The coordinate change
`T = funLeft e.symm` is injective and intertwines `toLin' M` with the reindexed
map. So `jordanSemisimplePart_intertwines` moves the identity for `ρ₀` back to
`ρ`, and injectivity of `T` cancels it.
