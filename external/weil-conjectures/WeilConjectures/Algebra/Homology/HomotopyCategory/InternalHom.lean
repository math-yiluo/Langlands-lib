/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-!
# The tensor-hom adjunction on the homotopy category

Let `C` be a monoidal closed preadditive category with countable products, in which the
tensor product of cochain complexes is defined, and let `K(C) = HomotopyCategory C (up ℤ)`.
For `P : K(C)`, the internal hom functor `CochainComplex.internalHom P.as` sends homotopic
morphisms to homotopic morphisms (`Homotopy.internalHomMap`), hence induces a functor
`HomotopyCategory.internalHom P : K(C) ⥤ K(C)`, and the tensor-hom adjunction
`CochainComplex.tensorHomAdjunction P.as` descends to an adjunction
`HomotopyCategory.tensorHomAdjunction P : tensorLeft P ⊣ internalHom P`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

universe v u

namespace HomotopyCategory

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (P : HomotopyCategory C (ComplexShape.up ℤ))

/-- `tensorLeft P` on `K(C)` lies over `tensorLeft P.as` on cochain complexes. -/
noncomputable instance : CatCommSq (tensorLeft P.as) (quotient _ _) (quotient _ _)
    (tensorLeft P) :=
  ⟨(Functor.Monoidal.commTensorLeft (quotient _ _) P.as).symm⟩

@[simp]
lemma catCommSq_iso_tensorLeft_hom_app (K : CochainComplex C ℤ) :
    (CatCommSq.iso (tensorLeft P.as) (quotient _ _) (quotient _ _) (tensorLeft P)).hom.app K =
      𝟙 _ := rfl

@[simp]
lemma catCommSq_iso_tensorLeft_inv_app (K : CochainComplex C ℤ) :
    (CatCommSq.iso (tensorLeft P.as) (quotient _ _) (quotient _ _) (tensorLeft P)).inv.app K =
      𝟙 _ := rfl

end

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (P : HomotopyCategory C (ComplexShape.up ℤ))

/-- The internal hom functor `K(C) ⥤ K(C)` induced by `CochainComplex.internalHom P.as`. -/
noncomputable def internalHom :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _ (CochainComplex.internalHom P.as ⋙ quotient _ _)
    (fun _ _ _ _ ⟨h⟩ ↦ eq_of_homotopy _ _ (h.internalHomMap P.as))

@[simp]
lemma internalHom_obj (Y : CochainComplex C ℤ) :
    (internalHom P).obj ((quotient _ _).obj Y) =
      (quotient _ _).obj (CochainComplex.internalHomObj P.as Y) := rfl

@[simp]
lemma internalHom_map_quotient_map {Y Y' : CochainComplex C ℤ} (k : Y ⟶ Y') :
    (internalHom P).map ((quotient _ _).map k) =
      (quotient _ _).map ((CochainComplex.internalHom P.as).map k) := rfl

/-- `internalHom P` lies over `CochainComplex.internalHom P.as`. -/
noncomputable def quotientCompInternalHomIso :
    quotient _ _ ⋙ internalHom P ≅ CochainComplex.internalHom P.as ⋙ quotient _ _ :=
  Quotient.lift.isLift _ _ _

@[simp]
lemma quotientCompInternalHomIso_hom_app (Y : CochainComplex C ℤ) :
    (quotientCompInternalHomIso P).hom.app Y = 𝟙 _ := rfl

@[simp]
lemma quotientCompInternalHomIso_inv_app (Y : CochainComplex C ℤ) :
    (quotientCompInternalHomIso P).inv.app Y = 𝟙 _ := rfl

/-- `internalHom P` on `K(C)` lies over `CochainComplex.internalHom P.as`. -/
noncomputable instance : CatCommSq (CochainComplex.internalHom P.as) (quotient _ _)
    (quotient _ _) (internalHom P) :=
  ⟨(quotientCompInternalHomIso P).symm⟩

@[simp]
lemma catCommSq_iso_internalHom :
    CatCommSq.iso (CochainComplex.internalHom P.as) (quotient _ _) (quotient _ _)
      (internalHom P) = (quotientCompInternalHomIso P).symm := rfl

/-- The tensor-hom adjunction on `K(C) = HomotopyCategory C (ComplexShape.up ℤ)`:
```
                tensorLeft P.as
      C(C) ─────────────────────────▶ C(C)
       │    ◀─────────────────────────  │
       │  CochainComplex.internalHom P.as │
       │ quotient                        │ quotient
       ▼        tensorLeft P             ▼
      K(C) ─────────────────────────▶ K(C)
            ◀─────────────────────────
                 internalHom P
```
It is obtained from `CochainComplex.tensorHomAdjunction P.as` by localization, since
`quotient` is a localization functor for the homotopy equivalences. -/
noncomputable def tensorHomAdjunction : tensorLeft P ⊣ internalHom P :=
  haveI := HasBinaryBiproducts.of_hasBinaryProducts (C := C)
  (CochainComplex.tensorHomAdjunction P.as).localization (quotient _ _)
    (HomologicalComplex.homotopyEquivalences _ _) (quotient _ _)
    (HomologicalComplex.homotopyEquivalences _ _) (tensorLeft P) (internalHom P)

@[simp]
lemma tensorHomAdjunction_unit_app (K : CochainComplex C ℤ) :
    (tensorHomAdjunction P).unit.app ((quotient _ _).obj K) =
      (quotient _ _).map ((CochainComplex.tensorHomAdjunction P.as).unit.app K) := by
  simp [tensorHomAdjunction, Adjunction.localization_unit_app]

@[simp]
lemma tensorHomAdjunction_counit_app (Y : CochainComplex C ℤ) :
    (tensorHomAdjunction P).counit.app ((quotient _ _).obj Y) =
      (quotient _ _).map ((CochainComplex.tensorHomAdjunction P.as).counit.app Y) := by
  simp [tensorHomAdjunction, Adjunction.localization_counit_app]

end HomotopyCategory
