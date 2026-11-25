/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
public import WeilConjectures.CategoryTheory.Derived.DerivedTowerCounitProjections
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
import all WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Exact tower functors and augmented counit evaluations

Source: blueprint main-20261015, chap-Smooth-purity, lemma-local-cohomology-right-adjoint--2,
returned Step 6 / immersion comparison Step 5; Stacks Derived Categories, Tags 015F,
04VG and 09T5, and Cohomology on Sites, Tag 0941
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation).

The four auxiliary maps are the displayed composites a, b, q and p of the node.
All comparisons and transitions reuse the existing exact-localization constructions.
The natural index n denotes positive level n + 1. Composition below is left to right.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB uC vC uD vD rA rB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ExactTowerAugmentedCounit

section TransitionLaws

variable (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]

private theorem transition_id (n : ℕᵒᵖ) :
    towerDerivedEvaluationTransition A (𝟙 n) = 𝟙 _ := by
  simp only [towerDerivedEvaluationTransition, Functor.map_id,
    NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id', Localization.liftNatTrans_id]

end TransitionLaws

section Maps

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The transported augmentation a = H̃(i) j⁻¹, with the specified canonical j.
Source: blueprint localization Step 6; Stacks 015F
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def augmentation {K : DerivedCategory A} {M : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K ⟶ M) :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M :=
  (ringedConstantTowerPullback F).inv.app K ≫
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map i

/-- The actual adjunction transpose b = L'(a) v', without assuming b invertible.
Source: blueprint localization Step 6; Stacks 09T5
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def transpose
    {L : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B}
    (adj : (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⊣ L)
    {K : DerivedCategory A} {M : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K ⟶ M) :
    F.mapDerivedCategory.obj K ⟶
      L.obj (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) :=
  adj.unit.app (F.mapDerivedCategory.obj K) ≫ L.map (augmentation F i)

/-- The level map qₙ = eₙ(i) sₙ⁻¹ for an arbitrary derived augmentation.
Source: blueprint localization Step 6; Stacks 015F
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def level {K : DerivedCategory A} {M : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K ⟶ M) (n : ℕ) :
    K ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.obj M :=
  (ringedConstantTowerEvaluation A (op n)).inv.app K ≫
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map i

/-- The normalized target projection pₙ = tₙ π'ₙ for the exact tower functor.
Source: blueprint localization Step 6; Stacks 09T5 and 0941
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def projection
    {L : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B}
    (π : ∀ n : ℕ, L ⟶ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory)
    (n : ℕ) (M : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    L.obj (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) ⟶
      F.mapDerivedCategory.obj (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.obj M) :=
  (π n).app (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) ≫
    (towerDerivedEvaluationInterchange F (op n)).hom.app M

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constant_coherence (n : ℕᵒᵖ) (K : DerivedCategory A) :
    (ringedConstantTowerEvaluation B n).inv.app (F.mapDerivedCategory.obj K) ≫
      ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        ((ringedConstantTowerPullback F).inv.app K) ≫
      (towerDerivedEvaluationInterchange F n).hom.app
        ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K) =
    F.mapDerivedCategory.map ((ringedConstantTowerEvaluation A n).inv.app K) := by
  let DA := (Functor.const ℕᵒᵖ : A ⥤ _)
  let EB := (evaluation ℕᵒᵖ B).obj n
  have heq :
      Functor.whiskerRight (ringedConstantTowerPullback F).hom EB.mapDerivedCategory ≫
          Functor.whiskerLeft F.mapDerivedCategory (ringedConstantTowerEvaluation B n).hom =
        Functor.whiskerLeft DA.mapDerivedCategory
            (towerDerivedEvaluationInterchange F n).hom ≫
          Functor.whiskerRight (ringedConstantTowerEvaluation A n).hom
            F.mapDerivedCategory := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro I
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    let DC := (DA.mapHomologicalComplex (.up ℤ)).obj I
    let FI := (F.mapHomologicalComplex (.up ℤ)).obj I
    let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
    let EA := (evaluation ℕᵒᵖ A).obj n
    let x := DA.mapDerivedCategoryFactors.hom.app I
    let y := F.mapDerivedCategoryFactors.hom.app I
    let z := FT.mapDerivedCategoryFactors.hom.app DC
    let eA := EA.mapDerivedCategoryFactors.hom.app DC
    let TC := (FT.mapHomologicalComplex (.up ℤ)).obj DC
    let BC := ((Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)).obj FI
    let c : TC ⟶ BC :=
      (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).inv.app I
    let eB := EB.mapDerivedCategoryFactors.hom.app TC
    let eBC := EB.mapDerivedCategoryFactors.hom.app BC
    let dB := (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app FI
    have hj : (ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj I) ≫
        (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y ≫ dB =
          FT.mapDerivedCategory.map x ≫ z ≫ DerivedCategory.Q.map c := rct_pull_fac F I
    have hc : EB.mapDerivedCategory.map (DerivedCategory.Q.map c) ≫ eBC = eB := by
      have h := EB.mapDerivedCategoryFactors_hom_naturality c
      have hid : (EB.mapHomologicalComplex (.up ℤ)).map c = 𝟙 FI := rfl
      rw [hid] at h
      erw [DerivedCategory.Q.map_id, Category.comp_id] at h
      exact h
    have hsA : (ringedConstantTowerEvaluation A n).hom.app (DerivedCategory.Q.obj I) =
        EA.mapDerivedCategory.map x ≫ eA := (rct_eval_fac A n I).symm
    have hsB : (ringedConstantTowerEvaluation B n).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫ y =
          EB.mapDerivedCategory.map
            ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y) ≫
          EB.mapDerivedCategory.map dB ≫ eBC := by
      have hn := (ringedConstantTowerEvaluation B n).hom.naturality y
      change EB.mapDerivedCategory.map
          ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y) ≫
          (ringedConstantTowerEvaluation B n).hom.app (DerivedCategory.Q.obj FI) =
        (ringedConstantTowerEvaluation B n).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫ y at hn
      exact hn.symm.trans (congrArg (fun g ↦ EB.mapDerivedCategory.map
        ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y) ≫ g)
          (rct_eval_fac B n FI).symm)
    have ht : (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj DC) ≫
        F.mapDerivedCategory.map eA ≫ y = EB.mapDerivedCategory.map z ≫ eB :=
      towerInterchange_fac F n DC
    have hn := (towerDerivedEvaluationInterchange F n).hom.naturality x
    change EB.mapDerivedCategory.map (FT.mapDerivedCategory.map x) ≫
        (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj DC) =
      (towerDerivedEvaluationInterchange F n).hom.app
        (DA.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
          F.mapDerivedCategory.map (EA.mapDerivedCategory.map x) at hn
    apply (cancel_mono y).mp
    calc
      _ = EB.mapDerivedCategory.map
          ((ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj I) ≫
            (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y ≫ dB) ≫ eBC := by
        simp only [Functor.map_comp, Category.assoc, hsB]
      _ = EB.mapDerivedCategory.map (FT.mapDerivedCategory.map x) ≫
          EB.mapDerivedCategory.map z ≫ eB := by
        rw [hj]
        simp only [Functor.map_comp, Category.assoc, hc]
      _ = EB.mapDerivedCategory.map (FT.mapDerivedCategory.map x) ≫
          (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj DC) ≫
            F.mapDerivedCategory.map eA ≫ y := by rw [ht]
      _ = _ := by
        rw [← Category.assoc, ← Category.assoc, hn, Category.assoc]
        rw [hsA, F.mapDerivedCategory.map_comp]
        simp only [Category.assoc]
  have h := NatTrans.congr_app heq K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  apply (cancel_epi ((ringedConstantTowerEvaluation B n).hom.app
    (F.mapDerivedCategory.obj K))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply (cancel_epi (EB.mapDerivedCategory.map
    ((ringedConstantTowerPullback F).hom.app K))).mp
  rw [← Category.assoc, ← Category.assoc, ← EB.mapDerivedCategory.map_comp,
    Iso.hom_inv_id_app, EB.mapDerivedCategory.map_id, Category.id_comp]
  rw [h, Category.assoc, ← F.mapDerivedCategory.map_comp,
    Iso.hom_inv_id_app, F.mapDerivedCategory.map_id]
  erw [Category.comp_id]

end Maps

end CategoryTheory.ExactTowerAugmentedCounit
