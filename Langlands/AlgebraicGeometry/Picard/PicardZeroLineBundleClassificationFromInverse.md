# Classification of Picard-zero line bundles from supplied tensor inverses

Module `Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationFromInverse`
proves `Langlands.AbelianScheme.PicardZeroLineBundleClassificationStatement`
from one extra hypothesis: every line bundle has a tensor inverse. The
hypothesis is passed as an explicit argument, so it is not an axiom. A
separate proof supplies it with the dual line bundle.

## Main theorem

`Langlands.AbelianScheme.picardZeroLineBundleClassification_of_inverse inverse`
has type `PicardZeroLineBundleClassificationStatement.{u}`. Its hypothesis is

`inverse : ∀ {X : Scheme.{u}} (L : LineBundle X), ∃ M : LineBundle X,
  Nonempty (tensorObj L.obj M.obj ≅ structureSheaf X)`.

So for every line bundle `L` on a scheme `X` in universe `u`, `inverse`
gives a line bundle `M` and an isomorphism of `O_X`-modules `L ⊗ M ≅ O_X`.
The theorem uses `inverse` only once, on the parameter scheme `T`.

## Helper lemmas

* `Langlands.GroupScheme.isTranslationInvariant_pullback_structure G M`:
  for a group scheme `G` over `S` and a line bundle `M` on `S`, the pullback
  of `M` along the structure map `G.X.hom` is translation invariant
  (`IsTranslationInvariant`). For each point `x`, the translation
  `translation G x` is a morphism over `S`. So pulling back `str^* M` along
  it is `str^* M` again, by `LineBundle.pullbackComp` and `Over.w`.
* `Langlands.AbelianScheme.isGeometricallyPicardZero_pullback_structure B M`:
  for an abelian scheme `B` over `S` and a line bundle `M` on `S`, the
  pullback of `M` along `B.X.hom` is Picard-zero on geometric fibres
  (`IsGeometricallyPicardZero`). On a geometric fibre `s : Spec K → S`, the
  restricted bundle is isomorphic to the pullback of `s^* M` along the
  structure map of the fibre. The isomorphism comes from `pullbackComp` and
  `pullback.condition`. The previous lemma and
  `GroupScheme.isTranslationInvariant_of_iso` then apply.
* `Langlands.AbelianScheme.isGeometricallyPicardZero_tensor_parameterPullback
  preservation A T N M hN`: let `N` be a line bundle on `T ×_S A` that is
  geometrically Picard-zero after transport along
  `(relativeSpaceSymmetry A.X.hom T).inv`, as in the statement. Let `M` be
  a line bundle on `T`. Then `N ⊗ pr_T^* M` satisfies the same condition.
  The transported tensor is the tensor of the transported factors
  (`LineBundle.pullbackTensorObjIso`). The transported `pr_T^* M` is the
  pullback of `M` along the structure map of `(baseChange T.hom).obj A`,
  because `pullbackSymmetry_inv_comp_fst` identifies the composite. That
  bundle is geometrically Picard-zero by the previous lemma. The Library's
  `isGeometricallyPicardZero_tensor` combines the two factors, and
  `isGeometricallyPicardZero_of_iso` transfers along the isomorphisms.

## Proof of the main theorem

Fix `preservation`, `A`, `hA`, `T`, `N` and the hypothesis `hN`. Write
`pr_T = (relativeProjection A.X.hom).app T` and
`e_T = (relativeSection A.X.hom (unitSection A) _).app T`. The Library
lemma `relativeSection_projection` gives `e_T ≫ pr_T = 𝟙`.

1. Apply `inverse` to `e_T^* N` on `T`. This gives a line bundle `M` on
   `T` and `evaluation : e_T^* N ⊗ M ≅ O_T`.
2. The Library's `LineBundle.normalize` turns `N ⊗ pr_T^* M` into a
   rigidified family `L` on `T ×_S A`, rigidified along `e_T` by means of
   `evaluation`. Its underlying bundle is `N ⊗ pr_T^* M` by definition.
3. `L` is a Picard-zero family. This is
   `isGeometricallyPicardZero_tensor_parameterPullback` applied to `hN`.
4. Take `φ := dualClassify A hA T` of the Picard-zero class of `L`. The
   Library's `dualClassifyPullbackIso` gives a rigidified isomorphism
   `φ^* P ≅ L`, where `φ^* P` is the relative rigidified pullback of
   `poincareFamily A hA`. Its underlying isomorphism of modules is `eP`.
5. The required isomorphism `N ≅ P_φ ⊗ pr_T^* (e_T^* N)` is built at the
   level of sheaves of modules (`ObjectProperty.isoMk`), as the composite
   of these steps:
   * `N ≅ N ⊗ O`, the inverse of `tensorRightUnitor`;
   * on the right factor, `O ≅ pr_T^* O_T`, the inverse of
     `pullbackUnitIso`;
   * then `pr_T^* O_T ≅ pr_T^* (M ⊗ e_T^* N)`, the pullback of the inverse
     of `evaluation` followed by `tensorComm`;
   * then `pr_T^* (M ⊗ e_T^* N) ≅ pr_T^* M ⊗ pr_T^* (e_T^* N)`, the
     comparison `pullbackTensorComparison`, invertible by `preservation`;
   * `N ⊗ (pr_T^* M ⊗ pr_T^* e_T^* N) ≅ (N ⊗ pr_T^* M) ⊗ pr_T^* e_T^* N`,
     the inverse of `tensorAssociator`;
   * finally, on the left factor, `N ⊗ pr_T^* M ≅ P_φ`, the inverse of
     `eP`.

The theorem asserts only existence of `φ` and of an isomorphism of
underlying line bundles, as the statement does. Nothing is claimed about
compatibility with rigidifications.

## Provenance

The statement's mathematical source is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, Chapter VI, (6.2)(ii); see the Markdown of
`PicardZeroLineBundleClassificationStatement`. This module implements
surjectivity in (6.2)(ii) for the Picard-zero subfunctor. Normalize the
bundle by the base twist, then classify it by the universal family. The
inverse bundle that the source writes as `ε^* L^{-1}` is the supplied `M`.

The theorem statement and the route follow a request from Worker 270 for
the proof of `PicardZeroLineBundleClassificationStatement` in task
`b71714f0-c50a-4258-94ac-e065ce455f61`. That proof supplies `inverse` from
the dual line bundle.
