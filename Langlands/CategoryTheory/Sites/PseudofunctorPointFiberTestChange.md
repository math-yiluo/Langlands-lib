# Point fibres after changing the test object

This module compares actual point fibres of a category-valued pseudofunctor
when the test object changes. It works with the published
`PseudofunctorPointFiber` module.

The setting is a category `C`, a pseudofunctor
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, an object `ξ` of `F` over `U`, and a test
object `η` of `F` over `T`. For `Z : Over T`, a point of the fibre is a pair
`⟨a, d⟩`. Here `a : Z.left ⟶ U` and `d : a^* ξ ≅ (Z.hom)^* η` is an actual
isomorphism. Restriction along `q : Z' ⟶ Z` uses the composition comparisons
of `F` (published `PseudofunctorPointFiber.restrict`). The point fibre
`presheaf F ξ η : (Over T)ᵒᵖ ⥤ Type _` collects these points with their
restriction maps.

Namespace: `Langlands.CategoryTheory.PseudofunctorPointFiberTestChange`.

## Changing the test object by an isomorphism

Fix an actual isomorphism `e : η ≅ η'` of test objects over `T`.

- `isoMapPoints F ξ e Z` sends `⟨a, d⟩` to `⟨a, d ≪≫ (Z.hom)^* e⟩`. The base
  map is unchanged.
- `isoMapPoints_restrict` shows that this map commutes with restriction. The
  proof uses naturality of the composition comparison
  `F.mapComp' Z.hom q.left Z'.hom` at `e.hom`.
- `isoMapPoints_symm` shows that `e.symm` undoes the map.
- `isoPointsEquiv F ξ e Z` is the resulting equivalence of point types.
- `isoPresheafIso F ξ e : presheaf F ξ η ≅ presheaf F ξ η'` is the natural
  isomorphism of full point fibres.

## Pulling back the test object

Fix `η` over `T` and a morphism `g : T' ⟶ T` in `C`. Write `g^* η` for
`(F.map g.op.toLoc).toFunctor.obj η`. `Over.map g : Over T' ⥤ Over T` sends
`Z` to `Z.left` with structure map `Z.hom ≫ g`.

- `compIso F η g Z : (Z.hom)^* (g^* η) ≅ (Z.hom ≫ g)^* η` is the inverse
  composition comparison `F.mapComp' g Z.hom (Z.hom ≫ g)`, evaluated at `η`.
- `basePointsEquiv F ξ η g Z` is an equivalence from points of the fibre of
  `g^* η` over `Z` to points of the fibre of `η` over `(Over.map g).obj Z`. It
  sends `⟨a, d⟩` to `⟨a, d ≪≫ compIso F η g Z⟩`, and its inverse composes with
  the inverse comparison. `basePointsEquiv_fst` records that the base map is
  unchanged.
- `basePointsEquiv_restrict` shows that the equivalence commutes with
  restriction along `q : Z' ⟶ Z` and along `(Over.map g).map q`. After
  unfolding `pullIso`, the remaining identity is the associativity coherence

  ```
  mapComp'(Z.hom, q.left, Z'.hom).inv_{g^* η} ≫ mapComp'(g, Z'.hom).inv_η
    = (q.left)^* (mapComp'(g, Z.hom).inv_η) ≫ mapComp'(Z.hom ≫ g, q.left).inv_η.
  ```

  Mathlib's `Pseudofunctor.whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv_app`
  gives it, with `f₀₁ = g`, `f₁₂ = Z.hom`, `f₂₃ = q.left`, `f₀₂ = Z.hom ≫ g`,
  `f₁₃ = Z'.hom` and `f = Z'.hom ≫ g`, all taken through `op` and `toLoc`.
- `basePresheafIso F ξ η g :
  presheaf F ξ (g^* η) ≅ (Over.map g).op ⋙ presheaf F ξ η` is the resulting
  natural isomorphism.

## Provenance

This is internal infrastructure for the finite-type Picard stack atlas task.
It formalizes two standard facts about point fibres. Isomorphic test objects
have isomorphic fibres. The fibre of a pulled-back test object is the
restriction of the original fibre along `Over.map`. No cited source theorem is
formalized.
