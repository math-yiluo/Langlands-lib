/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Constant strict towers and ringed direct image

Source: Stacks Project, Cohomology on Sites, Tag 0A07, lemma-Rf-commutes-with-Rlim,
diagram-topos proof, specialized to constant towers
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization).

The natural number n denotes positive tower level n+1. The comparisons supplied as
parameters below are characterized by their ordinary localization equations; they are
models of the specified derived operations, rather than additional geometric assumptions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.all false
set_option linter.unusedVariables false
universe u v w uA vA wA wTA uB vB wB wTB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Additivity of the exact constant tower functor, obtained from its preserved products.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerAdditive
    (A : Type uA) [Category.{vA} A] [Abelian A] :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Canonical evaluation of an exact constant strict tower, using the ordinary identity.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
def ringedConstantTowerEvaluation
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] (n : ℕᵒᵖ) :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.constCompEvaluationObj (D := A) n) ≪≫
      Functor.mapDerivedCategoryIdIso A

/-- The canonical constant-tower/exact-pullback interchange. Its ordinary components
are identities, as specified by compConstIso.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
def ringedConstantTowerPullback
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙
        (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_complex_refl
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (I : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app I = 𝟙 _ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_id_fac
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (I : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj I) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app I := by
  have hI : (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app I = 𝟙 _ := by
    ext; simp
  rw [Functor.mapDerivedCategoryIdIso_hom_app, hI]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_eval_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    (n : ℕᵒᵖ) (I : CochainComplex A ℤ) :
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app I) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) =
      (ringedConstantTowerEvaluation A n).hom.app (DerivedCategory.Q.obj I) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac
    (Functor.const ℕᵒᵖ : A ⥤ _) ((evaluation ℕᵒᵖ A).obj n) I
  simp only [rct_complex_refl, Functor.map_id, Category.comp_id] at hc
  simp only [ringedConstantTowerEvaluation, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, rct_id_fac]
  rw [Functor.mapDerivedCategoryNatIso_fac, ← hc]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rct_pull_fac
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex B ℤ) :
    (ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj I) ≫
        (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app I) ≫
        (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj I) =
      ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.map
          ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app I) ≫
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app
          (((Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).inv.app I) := by
  have hF := Functor.mapDerivedCategoryCompIso_fac
    (Functor.const ℕᵒᵖ : B ⥤ _) ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) I
  have hG := Functor.mapDerivedCategoryCompIso_fac F (Functor.const ℕᵒᵖ : A ⥤ _) I
  simp only [rct_complex_refl] at hF hG
  erw [Functor.map_id, Category.comp_id] at hF hG
  simp only [ringedConstantTowerPullback, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [hG, Functor.mapDerivedCategoryNatIso_fac, ← hF]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

end CategoryTheory
