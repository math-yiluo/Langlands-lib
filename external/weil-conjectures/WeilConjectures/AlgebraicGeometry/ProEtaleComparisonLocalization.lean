/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

/-! # ProEtaleComparisonLocalization

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def comparisonLowerStarLocalizationIso
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (V : X.Etale) :
    AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) X ⋙
      AlgebraicGeometry.Etale.localizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop ≅
    AlgebraicGeometry.ProEtale.localizationRestriction
      (ModuleCat.{u + 1} Λ) V.hom inferInstance ⋙
      AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) V.left :=
  NatIso.ofComponents (fun _ ↦
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _)))

set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_localization_eq
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (V : X.Etale) :
    (mateEquiv
      (AlgebraicGeometry.ProEtale.localizationRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) V.hom inferInstance)
      (AlgebraicGeometry.Etale.localizationRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) V.hom V.prop)
      (comparisonLowerStarLocalizationIso X Λ V).hom) =
    (AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso
      V.hom (ModuleCat.{u + 1} Λ)).hom := by
  apply NatTrans.ext
  funext F
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext T
  simp only [Functor.const_obj_obj, Functor.id_obj, Functor.comp_obj, mateEquiv_apply,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]
  dsimp [comparisonLowerStarLocalizationIso,
    AlgebraicGeometry.ProEtale.localizationRestrictionLowerStarAdjunction,
    AlgebraicGeometry.Etale.localizationRestrictionLowerStarAdjunction,
    AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso,
    AlgebraicGeometry.ProEtale.toProEtCompOverPullbackIso]
  dsimp [AlgebraicGeometry.ProEtale.lowerStar,
    AlgebraicGeometry.Etale.lowerStar,
    AlgebraicGeometry.ProEtale.comparisonLowerStar,
    AlgebraicGeometry.Etale.localizationRestriction,
    AlgebraicGeometry.ProEtale.localizationRestriction,
    Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft, Adjunction.op]
  dsimp [Functor.sheafPushforwardContinuous, MorphismProperty.Over.mapPullbackAdj]
  dsimp [ObjectProperty.isoMk, Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  simp only [Category.comp_id, Category.id_comp]
  rw [← F.obj.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Comma.comp_hom,
      MorphismProperty.Over.homMk_hom, Comma.comp_left, Over.homMk_left,
      MorphismProperty.Over.pullback_map_left, toProEt_map_hom, Category.assoc,
      limit.lift_π, PullbackCone.mk_π_app, MorphismProperty.Comma.id_hom, Comma.id_left]
  · change pullback.lift (𝟙 _) (pullback.snd T.unop.hom V.hom) _ ≫
      pullback.fst _ V.hom ≫ pullback.fst T.unop.hom V.hom =
        pullback.fst T.unop.hom V.hom
    rw [pullback.lift_fst_assoc, Category.id_comp]
  · change pullback.lift (𝟙 _) (pullback.snd T.unop.hom V.hom) _ ≫
      pullback.snd _ V.hom = pullback.snd T.unop.hom V.hom
    exact pullback.lift_snd _ _ _

private theorem leftMate_localization_isIso
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (V : X.Etale) :
    IsIso ((mateEquiv
      (AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
      (AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) V.left)).symm
      (comparisonLowerStarLocalizationIso X Λ V).hom) := by
  let adjX := AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X
  let adjV := AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) V.left
  let adjE := AlgebraicGeometry.Etale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) V.hom V.prop
  let adjP := AlgebraicGeometry.ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) V.hom inferInstance
  let δ := AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso
    V.hom (ModuleCat.{u + 1} Λ)
  have hb : mateEquiv adjP adjE (comparisonLowerStarLocalizationIso X Λ V).hom =
      TwoSquare.mk _ _ _ _ δ.hom := by
    refine NatTrans.ext (funext fun F ↦ ?_)
    exact congr_app (mate_localization_eq X Λ V) F
  have hb' := congrArg (mateEquiv adjP adjE).symm hb
  simp only [Equiv.symm_apply_apply] at hb'
  have heq := iterated_mateEquiv_conjugateEquiv_symm adjX adjV adjE adjP
    (TwoSquare.mk _ _ _ _ δ.hom)
  rw [← hb'] at heq
  have heq' := heq
  change ((mateEquiv adjX adjV).symm
      (comparisonLowerStarLocalizationIso X Λ V).hom) =
    (conjugateEquiv (adjX.comp adjP) (adjE.comp adjV)).symm δ.hom at heq'
  rw [heq']
  infer_instance

/-- If the local comparison counit is invertible, so is the restriction of the global
counit. This is the counit form of compatibility of comparison with etale localization.
Source: Stacks Project, Tag 099Y, proof, compatibility of comparison with restriction.
The identity-on-sections lower-star/restriction comparison has mate equal to the
source lowerStarCompComparisonLowerStarIso, as checked by the pullback projections.
The iterated mate identity then makes its mate under the comparison adjunctions
invertible. The mate counit equation identifies the restricted global counit, up to
these isomorphisms, with the local counit. Cancel the comparison isomorphisms.
(auxiliary; not a blueprint node) -/
theorem comparison_counit_restriction_isIso
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (V : X.Etale)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (h : IsIso ((AlgebraicGeometry.ProEtale.comparisonAdjunction
      (ModuleCat.{u + 1} Λ) V.left).counit.app
        ((AlgebraicGeometry.ProEtale.localizationRestriction
          (ModuleCat.{u + 1} Λ) V.hom inferInstance).obj F))) :
    IsIso ((AlgebraicGeometry.ProEtale.localizationRestriction
      (ModuleCat.{u + 1} Λ) V.hom inferInstance).map
        ((AlgebraicGeometry.ProEtale.comparisonAdjunction
          (ModuleCat.{u + 1} Λ) X).counit.app F)) := by
  let adjX := AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) X
  let adjV := AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) V.left
  let β := comparisonLowerStarLocalizationIso X Λ V
  let α := ((mateEquiv adjX adjV).symm β.hom)
  have : IsIso α := leftMate_localization_isIso X Λ V
  have : IsIso (adjV.counit.app
      ((AlgebraicGeometry.ProEtale.localizationRestriction
        (ModuleCat.{u + 1} Λ) V.hom inferInstance).obj F)) := h
  have heq := mateEquiv_counit_symm adjX adjV β.hom F
  have : IsIso (α.app
      ((AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) X).obj F) ≫
      (AlgebraicGeometry.ProEtale.localizationRestriction
        (ModuleCat.{u + 1} Λ) V.hom inferInstance).map (adjX.counit.app F)) := by
    rw [← heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.app _) _

end AlgebraicGeometry.Scheme
