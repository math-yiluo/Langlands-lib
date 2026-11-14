# A finite Galois splitting field of a form of the split `SO_{2n}`

## Galois-invariant local isomorphisms are independent

`LocalGroupIso.isIndependent_of_galois`: let `N / K` be a finite Galois
extension and `e` natural local group isomorphisms from `G` to `H` along
`Spec N ⟶ Spec K` (`ringTest K N`). Suppose that for every Galois
automorphism `σ`, every relative test `V`, every point `s : V ⟶ Spec N` and
every `g`, the values of `e` at `s` and at `s ≫ σ*` agree, where
`σ* = ringTestMap K σ`. Then `e` is independent of the cover point
(`IsIndependent`). The proof applies the published
`Cocycle.galoisPair_ext_tensor` to the two projections of
`Spec N ×_K Spec N` (the universal pair of points), using the naturality
of `e`. Every other pair of points `(a, b)` factors through this universal
pair.

## The split `SO_{2n}` and its base change

- `splitGroup K n` is the identity component of the split orthogonal group
  `OrthogonalMatrix.groupScheme (Fin n) K`, the split `SO_{2n}` over `K`.
- `splitBaseChangeIso K L n` identifies the base change of `splitGroup K n`
  along `Spec L ⟶ Spec K` with `splitGroup L n`, for a field extension `L`.
  It composes `IdentityComponent.baseChangeIso`, which says identity
  components commute with field extension, with the identity component of
  the comparison `OrthogonalMatrix.baseChangeModelIso` of the split
  orthogonal groups (`IdentityComponent.mapIso`).

## Finite Galois splitting

`exists_galois_localIso`: let `H` be an affine group scheme over `K` with an
isomorphism from its base change to the separable closure `K^s` onto the split
`SO_{2n}` over `K^s`. Then there are a finite Galois extension `N / K` and
local group isomorphisms from `H` to `splitGroup K n` along `Spec N ⟶ Spec K`.
The published `Descent.FiniteStage.exists_finiteSeparable_localIso_of_separableClosure`
gives such local isomorphisms along a finite separable subextension
`L ⊆ K^s`, once the target is rewritten with `splitBaseChangeIso`. The local
isomorphisms are then refined along `L ⟶ N`, where `N` is the normal closure
of `L` in `K^s`, which is finite Galois over `K`. This uses
`LocalGroupIso.refine` with the published `QuasiSplitInnerForm.coverRefinement`.

## Provenance

Derived. A form split by `K^s` is split by a finite Galois extension. The
independence criterion is the finite Galois case of fpqc descent for
morphisms (Galois descent). Both are standard. The Lean statements adapt the
published finite-stage and Galois-pair infrastructure to the split
`SO_{2n}`, which is a smooth affine group, so its identity component behaves
well under base change.
