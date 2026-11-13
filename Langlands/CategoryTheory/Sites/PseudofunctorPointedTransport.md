# Transport of pointings and composite restrictions of pointed deformations

This internal module adds two constructions to the published pointed
deformations `PseudofunctorPointedDeformations.Deformations F M T` of a
category-valued pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. All
declarations are in the namespace
`Langlands.CategoryTheory.PseudofunctorPointedTransport`.

Throughout, `T₀` is an object of `C` and `M` an object of `F` over `T₀`. For a
pointed test `T : Under T₀`, a pointed deformation over `T` is an object `Z` of
`F` over `T.right` together with an arrow `M ⟶ T.hom^* Z`. The published
`restrict F M q` restricts pointed deformations along an arrow `q : T ⟶ U` of
pointed tests, using the composition comparison `restrictionComparison F q`.

## Transport of a pointing

Let `s : V ⟶ W` be an arrow of pointed tests, `Z` an object of `F` over
`W.right`, `ξ` a pointed deformation over `V`, and
`e : s.right^* Z ≅ ξ.right` an isomorphism of objects over `V.right`.

- `transport F M s Z ξ e` is the pointed deformation over `W` with underlying
  object `Z`. Its pointing is the pointing `ξ.hom` of `ξ`, followed by the
  pullback of `e⁻¹` along `V.hom` and the inverse of the composition comparison
  `(restrictionComparison F s).inv` at `Z`.
- `transport_right` and `transport_hom` record the underlying object and the
  pointing.
- `transportIso F M s Z ξ e : (restrict F M s).obj (transport F M s Z ξ e) ≅ ξ`
  is the isomorphism of pointed deformations with underlying isomorphism `e`.
  Its compatibility with the pointings is the cancellation of the composition
  comparison with its inverse.

So an object over `W.right` whose restriction along `s` is identified with the
underlying object of `ξ` carries a pointing that makes its restriction
isomorphic to `ξ` as a pointed deformation.

## Composite restrictions

- `restrictCompObjIso F M q r qr h A`: for arrows `q : T ⟶ U`, `r : U ⟶ V` of
  pointed tests, `qr : T ⟶ V` with `h : q ≫ r = qr`, and a pointed deformation
  `A` over `V`, the isomorphism
  `(restrict F M q).obj ((restrict F M r).obj A) ≅ (restrict F M qr).obj A`.
  It is the inverse of the published `restrictCompIso` at `A`, followed by the
  identification along `h`. The two successive restrictions appear as nested
  objects rather than as a composite functor.
- `exists_restrict_of_comp`: if `(restrict F M qr).obj A ≅ ξ` for a pointed
  deformation `ξ` over `T`, then some pointed deformation `B` over `U`
  satisfies `(restrict F M q).obj B ≅ ξ`. Namely `B` is
  `(restrict F M r).obj A`.

## Provenance

Internal. These are formal consequences of the composition comparisons of a
pseudofunctor. The minimality step for Picard source stages
(`ArtinianPicardSourceMinimality`) and the extension step of the tower
ring-lifting argument (`ArtinianPicardTowerRingLifting`) use them. No
literature statement is transcribed.
