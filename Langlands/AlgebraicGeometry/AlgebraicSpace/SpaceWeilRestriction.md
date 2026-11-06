# Weil restriction of fppf sheaves and algebraic spaces

Author: Worker 105.

This module defines the Weil restriction functor that Brian Conrad uses in Lemma 5.10 and
Proposition 5.11(1) of *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp.17–18. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module contains
definitions and their defining identities only; it claims no property of the restriction.

Conrad's Lemma 5.10 (printed p.17) reads: "Let `R → R′` be a finite locally free ring
extension, and `X′` a (quasi-separated) algebraic space of finite type over `R′`. The Weil
restriction `X := Res_{R′/R}(X′)` as a functor on `R`-schemes is a (quasi-separated)
algebraic space of finite type over `R`." The functor in this sentence sends an `R`-scheme
`T` to `X′(T ⊗_R R′)`, the points of `X′` over the base change `T ×_{Spec R} Spec R′`.
This module builds that functor for actual fppf sheaves and the comparison maps of points.
Whether it is an algebraic space is the content of Lemma 5.10. That claim is stated
separately in `SpaceWeilRestrictionStatement.lean` and is not asserted here.

## Definitions

The objects are the Library's fppf sheaves `FppfSheaf S` on schemes over `S` and its
algebraic spaces `AlgebraicSpace S`, from `Basic.lean`.

- `weilRestriction g : FppfSheaf S' ⥤ FppfSheaf S`, for a morphism of schemes
  `g : S' ⟶ S`, is Mathlib's `Functor.sheafPushforwardContinuous` for the pullback functor
  `Over.pullback g : Over S ⥤ Over S'`. It sends a sheaf `F` to the presheaf
  `T ↦ F(T ×_S S')`, that is, `(Over.pullback g).op ⋙ F`. Mathlib proves that
  `Over.pullback g` is continuous for the slices `J.over S` and `J.over S'` of any
  Grothendieck topology `J` on a category with pullbacks
  (`Mathlib/CategoryTheory/Sites/Over.lean`). Applied to the fppf topology of schemes,
  this makes the restricted presheaf an fppf sheaf. `weilRestriction_obj_obj` and
  `weilRestriction_map_hom_app` record by `rfl` that sections over `T` and maps on them are
  those over `T ×_S S'`.
- `ringWeilRestriction R R'` is `weilRestriction (Spec.algebraMap R R')` for an
  `R`-algebra `R'`: Conrad's `Res_{R′/R}` on fppf sheaves over `Spec R′`.
- `FinitePresentationOverRing C X` says that an algebraic space `X` over `Spec C` has an
  étale surjective atlas by an actual scheme that is locally of finite presentation and
  quasi-compact over `Spec C`. It is the finite-presentation analogue of the published
  `FiniteTypeOverRing` (`Langlands/Global/AdelicSpaceLevelPointsStatement.lean`). For a
  quasi-separated `X` it is finite presentation in the Stacks Project's sense (locally of
  finite presentation, quasi-compact and quasi-separated), since over an affine base the
  space is quasi-compact exactly when it has a quasi-compact atlas.
- `ringWeilRestrictionSpace R R' X' h` is the algebraic space over `Spec R` with
  underlying sheaf `(ringWeilRestriction R R').obj X'.toSheaf`, for an algebraic space
  `X'` over `Spec R'` and a proof `h` that this sheaf is an algebraic space. The proof is an
  argument because being an algebraic space is what Lemma 5.10 asserts.
  `ringWeilRestrictionSpaceMap R R' hX hY f` is the morphism induced by `f : X' ⟶ Y'`.
- `ringWeilRestrictionPointsEquiv R R' A X' h` is the identification
  `Res_{R′/R}(X′)(A) ≃ X′(R′ ⊗[R] A)` for an `R`-algebra `A`. By definition, the
  `A`-points of the restriction are the sections of `X'` over
  `Spec A ×_{Spec R} Spec R′`. The equivalence pulls back along the Library's isomorphism
  `ringBaseChangeSpectrumIso R R' A : Spec A ×_{Spec R} Spec R′ ≅ Spec (R′ ⊗[R] A)` over
  `Spec R′` (`Langlands/AlgebraicGeometry/PointTopology/AffineBaseChangeCoordinates.lean`).
  `ringWeilRestrictionPointsEquiv_apply` gives the formula, and
  `ringWeilRestrictionPointsEquiv_map` its naturality in morphisms `f : X' ⟶ Y'`.
- The published `PointTopology.weilRestrictionTensorUnitTestIso R R'` is the isomorphism
  `Spec R′ ≅ Spec (R′ ⊗[R] R)` over `Spec R′` induced by the multiplication isomorphism
  `R′ ⊗[R] R ≃ R′` (`Algebra.TensorProduct.rid`).
- `ringWeilRestrictionBasePointsEquiv R R' X' h` is Conrad's identification
  `Res_{R′/R}(X′)(R) = X′(R′)` (printed p.18, Proposition 5.11(1)): the points equivalence
  at `A = R`, followed by pullback along the tensor-unit isomorphism.

## Relation to the source and derived content

Conrad defines `Res_{R′/R}(X′)` only as "a functor on `R`-schemes". Realizing it as the
pushforward of fppf sheaves along `Over.pullback`, the explicit point identifications
through `R′ ⊗[R] A`, the packaging as an algebraic space from a proof of the Lemma 5.10
property, and the predicate `FinitePresentationOverRing` are derived here. The module does
not need `R → R′` to be finite locally free; that hypothesis enters only in the statements.
Conrad's "finite presentation" for spaces over `R` is taken with his standing
quasi-separatedness convention; `FinitePresentationOverRing` itself does not include
quasi-separatedness, which the statements assume separately.

For an affine scheme, Conrad's proof (printed p.18) uses that the Weil restriction of an
affine scheme of finite type is an affine scheme of finite type. The Library's scheme-level
restriction (`AffineChartWeilRestrictionGluing.lean`, by another author) is not compared
with this functor here.
