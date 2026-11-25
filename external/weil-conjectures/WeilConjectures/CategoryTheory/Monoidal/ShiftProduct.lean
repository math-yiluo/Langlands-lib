/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Center.NegOnePow
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic

/-!
# Graded commutativity of the product of classes of the unit

Let `C` be a preadditive monoidal category with a shift by `ℤ` such that the tensor product
commutes with the shifts in both variables (`Functor.CommShift₂Int`): the two ways of moving
the shifts out of `X⟦p⟧ ⊗ Y⟦q⟧` differ by the sign `(-1) ^ (p * q)`. The morphisms
`𝟙_ C ⟶ (𝟙_ C)⟦n⟧` ("classes of degree `n`") have a product
```
       λ⁻¹             x ⊗ y                     ≅                    λ⟦i + j⟧
𝟙_ C ─────▶ 𝟙_ C ⊗ 𝟙_ C ──────▶ 𝟙_ C⟦i⟧ ⊗ 𝟙_ C⟦j⟧ ───▶ (𝟙_ C ⊗ 𝟙_ C)⟦i + j⟧ ───────▶ 𝟙_ C⟦i + j⟧
```
(`CategoryTheory.MonoidalCategory.shiftProduct`). If the unitors of `𝟙_ C` commute with the
shifts, this product is the Yoneda composite `x ≫ y⟦i⟧'` and it is graded commutative,
`y ⌣ x = (-1) ^ (i * j) x ⌣ y` (`CategoryTheory.MonoidalCategory.shiftProduct_comm`). This is
the Eckmann–Hilton argument: `x ⊗ y` factors as `(x ⊗ 1) ≫ (1 ⊗ y)` and as
`(1 ⊗ y) ≫ (x ⊗ 1)`, and the sign comes from the two orders of moving the shifts out.

## Main definitions

- `CategoryTheory.MonoidalCategory.shiftProduct`: the product of classes of the unit.

## Main statements

- `CategoryTheory.MonoidalCategory.shiftProduct_eq`: the product is the Yoneda composite.
- `CategoryTheory.MonoidalCategory.shiftProduct_comm`: the product is graded commutative.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [(curriedTensor C).CommShift₂Int]

/-- The product `x ⌣ y : 𝟙_ C ⟶ (𝟙_ C)⟦i + j⟧` of `x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧` and
`y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧`: the tensor product `x ⊗ y`, with the shifts moved out of the left
factor first, conjugated by the unitor `λ : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C`. -/
noncomputable def shiftProduct {i j : ℤ} (x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧) (y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧) :
    𝟙_ C ⟶ (𝟙_ C)⟦i + j⟧ :=
  (λ_ (𝟙_ C)).inv ≫ x ▷ 𝟙_ C ≫ (𝟙_ C)⟦i⟧ ◁ y ≫
    (((curriedTensor C).flip.obj ((𝟙_ C)⟦j⟧)).commShiftIso i).hom.app (𝟙_ C) ≫
    ((((curriedTensor C).obj (𝟙_ C)).commShiftIso j).hom.app (𝟙_ C))⟦i⟧' ≫
    (shiftFunctorAdd' C j i (i + j) (add_comm j i)).inv.app _ ≫ (λ_ (𝟙_ C)).hom⟦i + j⟧'

variable (C) in
/-- The unitors of `𝟙_ C` commute with the shifts: `𝟙_ C ⊗ (𝟙_ C)⟦n⟧ ≅ (𝟙_ C ⊗ 𝟙_ C)⟦n⟧`
followed by `λ⟦n⟧` is `λ`, and `(𝟙_ C)⟦n⟧ ⊗ 𝟙_ C ≅ (𝟙_ C ⊗ 𝟙_ C)⟦n⟧` followed by `ρ⟦n⟧`
is `ρ`. -/
structure UnitorsCommShift : Prop where
  leftUnitor (n : ℤ) : (((curriedTensor C).obj (𝟙_ C)).commShiftIso n).hom.app (𝟙_ C) ≫
    (λ_ (𝟙_ C)).hom⟦n⟧' = (λ_ ((𝟙_ C)⟦n⟧)).hom
  rightUnitor (n : ℤ) : (((curriedTensor C).flip.obj (𝟙_ C)).commShiftIso n).hom.app (𝟙_ C) ≫
    (ρ_ (𝟙_ C)).hom⟦n⟧' = (ρ_ ((𝟙_ C)⟦n⟧)).hom

namespace UnitorsCommShift

variable (h : UnitorsCommShift C)
include h

lemma leftUnitor_inv (n : ℤ) :
    (λ_ ((𝟙_ C)⟦n⟧)).inv ≫ (((curriedTensor C).obj (𝟙_ C)).commShiftIso n).hom.app (𝟙_ C) =
      (λ_ (𝟙_ C)).inv⟦n⟧' := by
  rw [← cancel_mono ((λ_ (𝟙_ C)).hom⟦n⟧'), assoc, h.leftUnitor, Iso.inv_hom_id,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]

lemma rightUnitor_inv (n : ℤ) :
    (ρ_ ((𝟙_ C)⟦n⟧)).inv ≫ (((curriedTensor C).flip.obj (𝟙_ C)).commShiftIso n).hom.app (𝟙_ C) =
      (ρ_ (𝟙_ C)).inv⟦n⟧' := by
  rw [← cancel_mono ((ρ_ (𝟙_ C)).hom⟦n⟧'), assoc, h.rightUnitor, Iso.inv_hom_id,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]

/-- `λ⁻¹ ≫ (x ⊗ 1)`, with the shift moved out, is `x` followed by `λ⁻¹⟦i⟧`. -/
lemma leftUnitor_inv_whiskerRight {i : ℤ} (x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧) :
    (λ_ (𝟙_ C)).inv ≫ x ▷ 𝟙_ C ≫
      (((curriedTensor C).flip.obj (𝟙_ C)).commShiftIso i).hom.app (𝟙_ C) =
      x ≫ (λ_ (𝟙_ C)).inv⟦i⟧' := by
  rw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc]
  exact congrArg (x ≫ ·) (h.rightUnitor_inv i)

/-- `λ⁻¹ ≫ (1 ⊗ y)`, with the shift moved out, is `y` followed by `λ⁻¹⟦j⟧`. -/
lemma leftUnitor_inv_whiskerLeft {j : ℤ} (y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧) :
    (λ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ y ≫
      (((curriedTensor C).obj (𝟙_ C)).commShiftIso j).hom.app (𝟙_ C) =
      y ≫ (λ_ (𝟙_ C)).inv⟦j⟧' := by
  rw [← leftUnitor_inv_naturality_assoc]
  exact congrArg (y ≫ ·) (h.leftUnitor_inv j)

/-- `λ⁻¹ ≫ (x ⊗ 1)`, with the shift moved out, followed by `λ⟦i⟧`, is `x`. -/
lemma leftUnitor_inv_whiskerRight_comp {i : ℤ} (x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧) :
    (λ_ (𝟙_ C)).inv ≫ x ▷ 𝟙_ C ≫
      (((curriedTensor C).flip.obj (𝟙_ C)).commShiftIso i).hom.app (𝟙_ C) ≫
        (λ_ (𝟙_ C)).hom⟦i⟧' = x := by
  rw [reassoc_of% h.leftUnitor_inv_whiskerRight x, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, comp_id]

/-- `λ⁻¹ ≫ (1 ⊗ y)`, with the shift moved out, followed by `λ⟦j⟧`, is `y`. -/
lemma leftUnitor_inv_whiskerLeft_comp {j : ℤ} (y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧) :
    (λ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ y ≫
      (((curriedTensor C).obj (𝟙_ C)).commShiftIso j).hom.app (𝟙_ C) ≫
        (λ_ (𝟙_ C)).hom⟦j⟧' = y := by
  rw [reassoc_of% h.leftUnitor_inv_whiskerLeft y, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, comp_id]

end UnitorsCommShift

/-- If the unitors commute with the shifts, the product `x ⌣ y` is the Yoneda composite
`x ≫ y⟦i⟧'`. -/
lemma shiftProduct_eq (h : UnitorsCommShift C) {i j : ℤ} (x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧)
    (y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧) :
    shiftProduct x y = x ≫ y⟦i⟧' ≫ (shiftFunctorAdd' C j i (i + j) (add_comm j i)).inv.app _ := by
  have h₁ := NatTrans.shift_app_comm ((curriedTensor C).flip.map y) i (𝟙_ C)
  have h₂ := (shiftFunctorAdd' C j i (i + j) (add_comm j i)).inv.naturality (λ_ (𝟙_ C)).hom
  dsimp at h₁ h₂
  rw [shiftProduct, ← reassoc_of% h₁, reassoc_of% h.leftUnitor_inv_whiskerRight]
  simp only [curriedTensor_obj_obj, ← h₂]
  simp only [← Functor.map_comp_assoc, h.leftUnitor_inv_whiskerLeft_comp]

/-- If the unitors commute with the shifts, the product `x ⌣ y` is, up to the sign
`(-1) ^ (i * j)`, the Yoneda composite `y ≫ x⟦j⟧'`. -/
lemma shiftProduct_eq_zsmul (h : UnitorsCommShift C) {i j : ℤ} (x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧)
    (y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧) :
    shiftProduct x y = (i * j).negOnePow • (y ≫ x⟦j⟧' ≫ (shiftFunctorComm C i j).hom.app _ ≫
      (shiftFunctorAdd' C j i (i + j) (add_comm j i)).inv.app _) := by
  have hc := (curriedTensor C).commShift₂_comm .int (𝟙_ C) (𝟙_ C) i j
  have hc' : (((curriedTensor C).flip.obj ((𝟙_ C)⟦j⟧)).commShiftIso i).hom.app (𝟙_ C) ≫
      ((((curriedTensor C).obj (𝟙_ C)).commShiftIso j).hom.app (𝟙_ C))⟦i⟧' =
      (i * j).negOnePow • ((((curriedTensor C).obj ((𝟙_ C)⟦i⟧)).commShiftIso j).hom.app
        (𝟙_ C) ≫ ((((curriedTensor C).flip.obj (𝟙_ C)).commShiftIso i).hom.app (𝟙_ C))⟦j⟧' ≫
          (shiftComm (𝟙_ C ⊗ 𝟙_ C) i j).hom) := by
    rw [reassoc_of% hc]
    simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, Units.smul_def, id_comp, smul_smul, ← Units.val_mul,
      ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, Units.val_one, one_smul]
    simp only [curriedTensor_obj_obj, Iso.inv_hom_id, comp_id]
  have h₁ := NatTrans.shift_app_comm ((curriedTensor C).map x) j (𝟙_ C)
  have h₂ := (shiftFunctorComm C i j).hom.naturality (λ_ (𝟙_ C)).hom
  have h₃ := (shiftFunctorAdd' C j i (i + j) (add_comm j i)).inv.naturality (λ_ (𝟙_ C)).hom
  dsimp at h₁ h₂ h₃
  rw [shiftProduct, ← whisker_exchange_assoc, reassoc_of% hc']
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Units.smul_def]
  congr 1
  simp only [assoc]
  rw [← reassoc_of% h₁, reassoc_of% h.leftUnitor_inv_whiskerLeft, shiftComm]
  simp only [curriedTensor_obj_obj, ← h₃, Iso.app_hom, ← reassoc_of% h₂]
  simp only [← Functor.map_comp_assoc, h.leftUnitor_inv_whiskerRight_comp]

/-- **The product of classes of the unit is graded commutative**: if the unitors commute with
the shifts, then `y ⌣ x = (-1) ^ (i * j) x ⌣ y` for `x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧` and
`y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧`, the two sides being compared along `(𝟙_ C)⟦j + i⟧ = (𝟙_ C)⟦i + j⟧`. -/
theorem shiftProduct_comm (h : UnitorsCommShift C) {i j : ℤ} (x : 𝟙_ C ⟶ (𝟙_ C)⟦i⟧)
    (y : 𝟙_ C ⟶ (𝟙_ C)⟦j⟧) :
    shiftProduct y x = (i * j).negOnePow • (shiftProduct x y ≫ eqToHom (by rw [add_comm])) := by
  rw [shiftProduct_eq h y x, shiftProduct_eq_zsmul h x y]
  simp only [Units.smul_def, Preadditive.zsmul_comp, smul_smul, ← Units.val_mul,
    ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, Units.val_one, one_smul, assoc,
    shiftFunctorComm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
  ]
  rw [← shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd'_inv_app_comp_eqToHom]

end CategoryTheory.MonoidalCategory
