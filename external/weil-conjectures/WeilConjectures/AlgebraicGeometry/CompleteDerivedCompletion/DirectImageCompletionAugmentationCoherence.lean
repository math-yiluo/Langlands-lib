/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Augmentation coherence for completed pullback

This is the strict derived-category square needed by the direct-image completion
unit.  Its proof is the localization calculation comparing the normalized cone
map with the degree-zero cone inclusion.
(blueprint: aux-weil-pbc-direct-image-augmentation-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem directImage_strictPullReduction_inr
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    ((pull l E f).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr ((complexPowerMap l E Y).app P)) ≫
      (strictPullReduction l E f).hom.app P =
      (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).symm (.up ℤ)).hom.app P ≫
        CochainComplex.mappingCone.inr ((complexPowerMap l E X).app
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapHomologicalComplex
            (.up ℤ)).obj P)) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext n
  exact (strictPullReduction_existsUnique l E f).exists.choose_spec P i n.unop |>.2

private theorem directImage_constantInterchange_factors
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
    let cY := (constant l E Y).mapDerivedCategoryFactors.hom.app P
    (constantInterchange l E H).hom.app (DerivedCategory.Q.obj P) ≫
        (pull l E f).mapDerivedCategory.map cY ≫
        (pull l E f).mapDerivedCategoryFactors.hom.app
          (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) =
      (dconstant l E X).map
          (H.mapDerivedCategoryFactors.hom.app P) ≫
        (constant l E X).mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).hom.app P) := by
  dsimp only
  let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors H
    (constant l E X) P
  dsimp only [H] at hF
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors
    (constant l E Y) (pull l E f) P
  dsimp [constantInterchange]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hG, Functor.mapDerivedCategoryNatIso_fac, ← hF]
  simp only [Iso.hom_inv_id_app_assoc, Category.assoc]
  simp only [NatIso.mapHomologicalComplex]

private theorem directImage_constantInterchange_inverse_factors
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
    (pull l E f).mapDerivedCategory.map
        ((constant l E Y).mapDerivedCategoryFactors.hom.app P) ≫
      (pull l E f).mapDerivedCategoryFactors.hom.app
        (((constant l E Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P) =
      (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫
        (dconstant l E X).map (H.mapDerivedCategoryFactors.hom.app P) ≫
        (constant l E X).mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj P) := by
  dsimp only
  let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  have hforward := directImage_constantInterchange_factors l E f P
  have hh := congrArg
    (fun q ↦ (constantInterchange l E H).inv.app (DerivedCategory.Q.obj P) ≫ q ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P))
    hforward
  have hsymm :
      NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ) =
        (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ H) (.up ℤ)).symm := rfl
  dsimp only [H] at hsymm hh
  rw [hsymm] at hh ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.symm_hom,
    ← Functor.map_comp, Iso.hom_inv_id_app] at hh
  erw [(DerivedCategory.Q (C := Tow l E X)).map_id, Category.comp_id] at hh
  exact hh

private theorem directImage_augmentation_factors (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (augmentation l E T).app (DerivedCategory.Q.obj P) ≫ (redFactors l E T).hom.app P =
      (constant l E T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((strictAugmentation l E T).app P) := by
  simp only [augmentation, Localization.liftNatTrans_app, Functor.whiskerRight_app]
  change (_ ≫ DerivedCategory.Q.map ((strictAugmentation l E T).app P) ≫
    (redFactors l E T).inv.app P) ≫ (redFactors l E T).hom.app P = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simp only [Localization.Lifting.iso]
  exact congrArg (fun g ↦ (constant l E T).mapDerivedCategoryFactors.hom.app P ≫ g)
    (Category.comp_id (DerivedCategory.Q.map ((strictAugmentation l E T).app P)))

/-- The canonical pullback/reduction comparison carries the degree-zero
augmentation through constant towers.  This is obtained by expanding
`Localization.liftNatTrans` and applying the inr equation for mapping cones;
the normalization equation `IsPullReduction` then identifies the two localized
maps.  It is independent of any choice of K-injective representative.
(blueprint: aux-weil-pbc-direct-image-augmentation-coherence) -/
theorem directImage_augmentation_pullReduction_coherence :
    ∀ M : DerivedCategory (AdicCompletion.Modules l E Y),
      (dpull l E f).map ((augmentation l E Y).app M) ≫
          (pullReduction l E f).hom.app M =
        (constantInterchange l E
          (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv.app M ≫
          (augmentation l E X).app ((dpullModule l E f).obj M) := by
  let H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let α : dconstant l E Y ⋙ dpull l E f ⟶
      dpullModule l E f ⋙ red l E X :=
    Functor.whiskerRight (augmentation l E Y) (dpull l E f) ≫
      (pullReduction l E f).hom
  let β : dconstant l E Y ⋙ dpull l E f ⟶
      dpullModule l E f ⋙ red l E X :=
    (constantInterchange l E H).inv ≫
      Functor.whiskerLeft (dpullModule l E f) (augmentation l E X)
  have hab : α = β := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ))
    intro P
    dsimp only [α, β, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    apply (cancel_mono ((red l E X).map
      (H.mapDerivedCategoryFactors.hom.app P) ≫
      (redFactors l E X).hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj P))).1
    simp only [Category.assoc]
    rw [← reassoc_of% ((augmentation l E X).naturality
      (H.mapDerivedCategoryFactors.hom.app P)),
      directImage_augmentation_factors]
    have haug := directImage_augmentation_factors l E Y P
    have haug' : (augmentation l E Y).app (DerivedCategory.Q.obj P) =
        (constant l E Y).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((strictAugmentation l E Y).app P) ≫
          (redFactors l E Y).inv.app P := by
      rw [← reassoc_of% haug, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    rw [haug']
    simp only [Functor.map_comp, Category.assoc]
    have hpr := (pullReduction_existsUnique l E f).exists.choose_spec P
    dsimp only [H, pullReduction]
    rw [hpr]
    have hfac := (pull l E f).mapDerivedCategoryFactors_hom_naturality
      ((strictAugmentation l E Y).app P)
    dsimp only [dpull]
    rw [reassoc_of% hfac, ← Functor.map_comp]
    have hinr := directImage_strictPullReduction_inr l E f P
    change ((pull l E f).mapHomologicalComplex (.up ℤ)).map
        ((strictAugmentation l E Y).app P) ≫ (strictPullReduction l E f).hom.app P =
      (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ H).symm (.up ℤ)).hom.app P ≫
        (strictAugmentation l E X).app ((H.mapHomologicalComplex (.up ℤ)).obj P) at hinr
    rw [hinr, Functor.map_comp]
    have hh := congrArg
      (fun q ↦ q ≫ DerivedCategory.Q.map ((strictAugmentation l E X).app
        ((H.mapHomologicalComplex (.up ℤ)).obj P)))
      (directImage_constantInterchange_inverse_factors l E f P)
    simpa only [Category.assoc] using hh
  intro M
  exact congr_app hab M

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
