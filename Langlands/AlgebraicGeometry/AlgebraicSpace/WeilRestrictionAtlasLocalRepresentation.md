# Local representation of restricted étale surjective schemes

Author: Worker 185.

This module proves the internal input `RepresentationInput` of
`WeilRestrictionAtlasReduction`, and so completes the affine-atlas step in
Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Lemma 5.10, printed pp.17–18 (registered source
`conrad-2011-weil-grothendieck-adelic-points`). There Conrad represents the
restriction of scalars of a quasi-affine scheme and applies it to étale
surjective quasi-affine charts. Here the restriction of an étale surjective
quasi-compact separated scheme is represented locally on the base by such
restrictions and glued. The argument is written for this Library and is not
copied from the source.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionAtlas`. Throughout,
`R'` is a finite projective `R`-algebra, `π = Spec.algebraMap R R'`, `V` is a
scheme over `Spec R`, and `Y` is a scheme over `V.left ×_{Spec R} Spec R'`.

## The restricted presheaf

`restrictedPresheaf R R' Y` is the presheaf on schemes over `V.left` given by
`(Over.pullback (pullback.fst V.hom π)).op ⋙ (schemeYoneda _).obj Y`.
`restrictedPresheaf_isSheaf` states that it is an fppf sheaf: it is the
underlying presheaf of the Library's sheaf-level Weil restriction
`weilRestriction (pullback.fst V.hom π)` of the represented fppf sheaf of `Y`.
This lemma does not use finiteness or projectivity of `R'`.

## Affine charts

`exists_chart_representation` assumes that `Y.hom` is étale, surjective,
quasi-compact and separated. For a commutative ring `A` and a morphism
`j : Spec A ⟶ V.left`, it gives a scheme `H` over `Spec A` that is étale and
surjective, with an isomorphism from its represented presheaf to the
restriction `(Over.map j).op ⋙ restrictedPresheaf R R' Y` to schemes over
`Spec A`. Proof:

1. Make `A` an `R`-algebra through `j ≫ V.hom` (`Spec.preimage`), and let
   `D = A ⊗[R] R'`. It is an `A`-algebra through the left factor,
   `a ↦ a ⊗ 1`, and an `R'`-algebra through the right factor,
   `r' ↦ 1 ⊗ r'` (the module's local instance
   `Algebra.TensorProduct.rightAlgebra`); these give the two projections
   `Spec.algebraMap A D` and `Spec.algebraMap R' D`. The Library
   square `isPullback_weilRestrictionTensor` shows that `Spec D`, with these
   projections, is the fibre product of `Spec A` and `Spec R'` over `Spec R`.
   Cancelling the pullback
   square of `V.hom` and `π` (`IsPullback.of_right'`) gives
   `j' : Spec D ⟶ V.left ×_{Spec R} Spec R'` and a pullback square `hj` with
   sides `j'`, `Spec.algebraMap A D`, `pullback.fst V.hom π` and `j`.
2. Let `Yj` be the base change of `Y` along `j'`, a scheme over `Spec D`. It is
   étale, surjective, quasi-compact and separated over `Spec D` by base change.
   Hence it is locally of finite type and locally quasi-finite
   (`Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale`), and `Yj.left`
   is compact because `Spec D` is. Zariski's main theorem in the Library's
   quasi-affine form,
   `LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite`, shows that
   `Yj.left` is quasi-affine.
3. Take `H = affineChartWeilRestriction A D Yj`, the Library's glued
   affine-chart Weil restriction. It is étale over `Spec A` by the instance of
   `AffineChartWeilRestrictionEtale` and surjective by
   `affineChartWeilRestriction_surjective`.
4. The isomorphism is the composite of three Library isomorphisms:
   `quasiAffineWeilRestrictionPresheafIso A D Yj` (representability of the
   Weil restriction of a quasi-affine scheme), the base-change identification
   `schemeYonedaBaseChangeIso j' Y` restricted along
   `Over.pullback (Spec.algebraMap A D)`, and the inverse of
   `weilRestrictionBaseChangePresheafIso hj`, which commutes restriction with
   the base change of the square `hj`.

## Gluing

`representationInput` proves `RepresentationInput`. For `V`, `Y` as above with
`Y.hom` étale, surjective, quasi-compact and separated, apply
`exists_chart_representation` to every chart `Spec A ⟶ V.left` of the affine
open cover `V.left.affineOpenCover`. The restricted presheaf is an fppf sheaf
with scheme representatives over an open cover, so the Library gluing theorem
`LocalRepresentation.exists_representation` represents it by a scheme `W` over
`V.left`. Étaleness and surjectivity are local on the target, and
`LocalRepresentation.property_of_local_representations` transfers them from the
chart representatives to `W.hom`.
