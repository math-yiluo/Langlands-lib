/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Ordinary tensor evaluation for ringed-site complexes

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08JJ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

attribute [local irreducible] homComplexFunctor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance instMonoidalPreadditiveRingedComplexTensorEvaluation :
    MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

local instance instHasColimitsOfSizeRingedComplexTensorEvaluation :
    HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

/-- The ordinary product Hom, with its specified sign, is right adjoint to total tensor.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
@[irreducible]
def ringedComplexHomAdjunction (P : ringedSiteComplex O) :
    tensorLeft P ⊣ (homComplexFunctor (R := O)).obj (op P) :=
  (CochainComplex.tensorHomAdjunction P).ofNatIsoRight
    (homComplexFunctorObjIsoInternalHom P).symm

/-- The closed structure using the ordinary product Hom and its signed adjunction.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
@[instance_reducible]
def ringedComplexClosed : MonoidalClosed (ringedSiteComplex O) where
  closed P :=
    { rightAdj := (homComplexFunctor (R := O)).obj (op P)
      adj := ringedComplexHomAdjunction O P }

attribute [local instance] ringedComplexClosed

/-- The transpose has the Koszul sign imposed by the product-Hom convention.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
theorem ringedComplexCurry_component {P K N : ringedSiteComplex O} (g : P ⊗ K ⟶ N)
    (n p q : ℤ) (h : p + n = q) :
    (MonoidalClosed.curry g).f n ≫ homComplexπ P N n p q h =
      (p * n).negOnePow • MonoidalClosed.curry
        (HomologicalComplex.ιTensorObj P K p n q h ≫ g.f q) := by
  change ((ringedComplexHomAdjunction O P).homEquiv K N g).f n ≫ _ = _
  unfold ringedComplexHomAdjunction
  erw [Adjunction.homEquiv_ofNatIsoRight_apply,
    CochainComplex.tensorHomAdjunction_homEquiv, HomologicalComplex.comp_f, Category.assoc]
  change _ ≫ internalHomObjToHomComplexX P N n ≫ homComplexIhomπ P N n p q h = _
  rw [internalHomObjToHomComplexX_π, Linear.comp_units_smul,
    CochainComplex.internalHomEquiv_f_π]

private theorem hom_source_component {P P' N : ringedSiteComplex O} (f : P' ⟶ P)
    (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor (R := O)).map f.op).app N).f n ≫
        homComplexπ P' N n p q h =
      homComplexπ P N n p q h ≫ SheafOfModules.homObjMap (R := O) (f.f p) (𝟙 (N.X q)) := by
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
    homComplexFunctor_map_f_π f (𝟙 N) n p q h

private theorem curry_source {P P' K N : ringedSiteComplex O} (f : P' ⟶ P)
    (g : P ⊗ K ⟶ N) :
    MonoidalClosed.curry (f ▷ K ≫ g) =
      MonoidalClosed.curry g ≫ ((homComplexFunctor (R := O)).map f.op).app N := by
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, Category.assoc, hom_source_component,
    ← Category.assoc, ringedComplexCurry_component, ringedComplexCurry_component,
    Linear.units_smul_comp]
  congr 1
  erw [← SheafOfModules.pre_app (R := O) (f.f p) (N.X q),
    MonoidalClosed.curry_pre_app]
  congr 1
  rw [HomologicalComplex.comp_f, ← Category.assoc,
    CochainComplex.Monoidal.ι_whiskerRight, Category.assoc]

private theorem pre_eq {P P' : ringedSiteComplex O} (f : P' ⟶ P)
    (N : ringedSiteComplex O) :
    (MonoidalClosed.pre f).app N = ((homComplexFunctor (R := O)).map f.op).app N := by
  rw [← MonoidalClosed.curry_uncurry ((MonoidalClosed.pre f).app N),
    MonoidalClosed.uncurry_pre, curry_source,
    ← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry, Category.id_comp]

section Generic

variable {D : Type v} [Category.{w} D] [MonoidalCategory D]
  [MonoidalClosed D] [BraidedCategory D]

private theorem evaluation_naturality (P : D) {N M : D} (f : N ⟶ M) :
    f ▷ ((ihom P).obj (𝟙_ D)) ≫ (β_ M _).hom ≫
        MonoidalClosed.ihomUnitTensorToIhom P M =
      (β_ N _).hom ≫ MonoidalClosed.ihomUnitTensorToIhom P N ≫ (ihom P).map f := by
  rw [BraidedCategory.braiding_naturality_left_assoc]
  congr 1
  dsimp only [MonoidalClosed.ihomUnitTensorToIhom]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_right]
  congr 1
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  dsimp only [Functor.id_obj]
  rw [leftUnitor_naturality]

private theorem evaluation_source {P P' : D} (f : P' ⟶ P) (N : D) :
    N ◁ (MonoidalClosed.pre f).app (𝟙_ D) ≫ (β_ N _).hom ≫
        MonoidalClosed.ihomUnitTensorToIhom P' N =
      (β_ N _).hom ≫ MonoidalClosed.ihomUnitTensorToIhom P N ≫
        (MonoidalClosed.pre f).app N := by
  rw [BraidedCategory.braiding_naturality_right_assoc]
  congr 1
  dsimp only [MonoidalClosed.ihomUnitTensorToIhom]
  rw [← MonoidalClosed.curry_natural_left, MonoidalClosed.curry_pre_app]
  congr 1
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, MonoidalClosed.id_tensor_pre_app_comp_ev,
    comp_whiskerRight_assoc, associator_inv_naturality_left_assoc]

private theorem evaluation_unit (N : D) :
    (ρ_ N).inv ≫ N ◁ MonoidalClosed.unitNatIso.hom.app (𝟙_ D) ≫
        (β_ N _).hom ≫ MonoidalClosed.ihomUnitTensorToIhom (𝟙_ D) N =
      MonoidalClosed.unitNatIso.hom.app N := by
  rw [BraidedCategory.braiding_naturality_right_assoc]
  dsimp only [MonoidalClosed.ihomUnitTensorToIhom]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left,
    ← MonoidalClosed.curry_natural_left, MonoidalClosed.unitNatIso_hom_app N]
  congr 1
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    MonoidalClosed.whiskerLeft_unitNatIso_hom_app_ihom_ev_app,
    braiding_tensorUnit_right]
  monoidal

end Generic

/-- Canonical evaluation, with coefficients on the left and the strict Hom dual on the right.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
def ringedComplexTensorEvaluation (P N : ringedSiteComplex O) :
    ((ringedKoszulTensor O).obj N).obj
        (homComplex (R := O) P (ringedSiteRingComplex O)) ⟶ homComplex (R := O) P N :=
  (β_ N ((ihom P).obj (𝟙_ (ringedSiteComplex O)))).hom ≫
    MonoidalClosed.ihomUnitTensorToIhom P N

/-- Evaluation is natural in the coefficient complex.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
theorem ringedComplexTensorEvaluation_naturality (P : ringedSiteComplex O)
    {N M : ringedSiteComplex O} (f : N ⟶ M) :
    ((ringedKoszulTensor O).map f).app _ ≫ ringedComplexTensorEvaluation O P M =
      ringedComplexTensorEvaluation O P N ≫
        ((homComplexFunctor (R := O)).obj (op P)).map f := by
  exact evaluation_naturality P f

/-- Evaluation against a dualizable complex is invertible.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
theorem ringedComplexTensorEvaluation_isIso (P N : ringedSiteComplex O)
    (hP : IsDualizable P) : IsIso (ringedComplexTensorEvaluation O P N) := by
  let _ := hP.some
  let _ : HasLeftDual P := BraidedCategory.hasLeftDualOfHasRightDual
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom (ᘁP) P N
  exact IsIso.comp_isIso

/-- Evaluation commutes with precomposition by any chain map.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
theorem ringedComplexTensorEvaluation_source {P P' : ringedSiteComplex O}
    (f : P' ⟶ P) (N : ringedSiteComplex O) :
    ((ringedKoszulTensor O).obj N).map
        (((homComplexFunctor (R := O)).map f.op).app (ringedSiteRingComplex O)) ≫
        ringedComplexTensorEvaluation O P' N =
      ringedComplexTensorEvaluation O P N ≫
        ((homComplexFunctor (R := O)).map f.op).app N := by
  have h := evaluation_source f N
  rw [pre_eq, pre_eq] at h
  exact h

/-- The transpose of the ordinary tensor left unitor.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
@[irreducible]
def ringedComplexHomUnit (N : ringedSiteComplex O) :
    N ⟶ homComplex (R := O) (ringedSiteRingComplex O) N :=
  MonoidalClosed.unitNatIso.hom.app N

/-- The Hom unit is the transpose of the tensor left unitor.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
theorem ringedComplexHomUnit_eq_curry (N : ringedSiteComplex O) :
    ringedComplexHomUnit O N = MonoidalClosed.curry (λ_ N).hom := by
  unfold ringedComplexHomUnit
  exact MonoidalClosed.unitNatIso_hom_app N

/-- The tensor-Hom comparison respects the unit of the closed adjunction.
Source: Stacks 08JJ (auxiliary; not a blueprint node). -/
theorem ringedComplexTensorEvaluation_unit (N : ringedSiteComplex O) :
    (ringedKoszulRightUnitIso O N).inv ≫
        ((ringedKoszulTensor O).obj N).map
          (ringedComplexHomUnit O (ringedSiteRingComplex O)) ≫
        ringedComplexTensorEvaluation O (ringedSiteRingComplex O) N =
      ringedComplexHomUnit O N := by
  unfold ringedComplexHomUnit
  exact evaluation_unit N

end CategoryTheory
