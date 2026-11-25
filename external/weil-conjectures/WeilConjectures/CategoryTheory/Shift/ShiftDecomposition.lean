/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Data.Fintype.BigOperators

/-!
# Decompositions into finite sums of shifts of an object

Let `C` be a preadditive category with a shift by `ℤ` and `E` an object of `C`. A
*decomposition of `P` into shifts of `E`* (`CategoryTheory.ShiftDecomposition E P`) is a finite
family of inclusions `E⟦nⱼ⟧ ⟶ P` and projections `P ⟶ E⟦nⱼ⟧` exhibiting `P` as the direct sum
`⨁ⱼ E⟦nⱼ⟧`. Such decompositions are transported along isomorphisms, shifts and binary direct sums,
and exist for zero objects and for `E` itself. A decomposition is a bilimit bicone
(`CategoryTheory.ShiftDecomposition.isBilimitBicone`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- A decomposition of `P` as a finite direct sum `⨁ⱼ E⟦nⱼ⟧` of shifts of `E`. -/
structure ShiftDecomposition (E P : C) where
  /-- The index type of the summands. -/
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- The shift of the summand `j`. -/
  deg : ι → ℤ
  /-- The inclusion of the summand `j`. -/
  incl (j : ι) : (shiftFunctor C (deg j)).obj E ⟶ P
  /-- The projection onto the summand `j`. -/
  proj (j : ι) : P ⟶ (shiftFunctor C (deg j)).obj E
  total : ∑ j, proj j ≫ incl j = 𝟙 P
  incl_proj_self (j : ι) : incl j ≫ proj j = 𝟙 _
  incl_proj_of_ne (j j' : ι) (h : j ≠ j') : incl j ≫ proj j' = 0

namespace ShiftDecomposition

attribute [instance] fintype decEq

variable {E P Q : C}

/-- A decomposition transported along an isomorphism. -/
def ofIso (D : ShiftDecomposition E P) (e : P ≅ Q) : ShiftDecomposition E Q where
  ι := D.ι
  deg := D.deg
  incl j := D.incl j ≫ e.hom
  proj j := e.inv ≫ D.proj j
  total := by
    have h : ∑ j, D.proj j ≫ D.incl j ≫ e.hom = e.hom := by
      simp only [← Category.assoc, ← Preadditive.sum_comp, D.total, Category.id_comp]
    simp only [Category.assoc, ← Preadditive.comp_sum, h, Iso.inv_hom_id]
  incl_proj_self j := by simp [D.incl_proj_self]
  incl_proj_of_ne j j' h := by simp [D.incl_proj_of_ne j j' h]

/-- The empty decomposition of a zero object. -/
def ofIsZero (hP : IsZero P) : ShiftDecomposition E P where
  ι := Empty
  deg := Empty.elim
  incl := fun j ↦ j.elim
  proj := fun j ↦ j.elim
  total := hP.eq_of_src _ _
  incl_proj_self := fun j ↦ j.elim
  incl_proj_of_ne := fun j ↦ j.elim

/-- The bicone with cone point `P` and summands `E⟦nⱼ⟧` of a decomposition of `P`. -/
@[simps]
def bicone (D : ShiftDecomposition E P) : Bicone fun j ↦ (shiftFunctor C (D.deg j)).obj E where
  pt := P
  π := D.proj
  ι := D.incl
  ι_π j j' := by
    split_ifs with h
    · subst h
      rw [D.incl_proj_self, eqToHom_refl]
    · exact D.incl_proj_of_ne j j' h

/-- The bicone of a decomposition is a bilimit: `P` is the biproduct `⨁ⱼ E⟦nⱼ⟧`. -/
def isBilimitBicone (D : ShiftDecomposition E P) : D.bicone.IsBilimit :=
  isBilimitOfTotal _ D.total

variable (E) in
/-- The decomposition of `E` with the single summand `E⟦0⟧`. -/
noncomputable def self : ShiftDecomposition E E where
  ι := Unit
  deg _ := 0
  incl _ := (shiftFunctorZero C ℤ).hom.app E
  proj _ := (shiftFunctorZero C ℤ).inv.app E
  total := by simp
  incl_proj_self _ := by simp
  incl_proj_of_ne _ _ h := absurd (Subsingleton.elim _ _) h

/-- The decomposition of `P⟦a⟧` obtained by shifting a decomposition of `P`. -/
noncomputable def shift (D : ShiftDecomposition E P) (a : ℤ) :
    ShiftDecomposition E ((shiftFunctor C a).obj P) where
  ι := D.ι
  deg j := D.deg j + a
  incl j := (shiftFunctorAdd' C (D.deg j) a _ rfl).hom.app E ≫ (shiftFunctor C a).map (D.incl j)
  proj j := (shiftFunctor C a).map (D.proj j) ≫ (shiftFunctorAdd' C (D.deg j) a _ rfl).inv.app E
  total := by
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, ← Functor.map_sum,
      D.total, CategoryTheory.Functor.map_id]
  incl_proj_self j := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, D.incl_proj_self,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  incl_proj_of_ne j j' h := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, D.incl_proj_of_ne j j' h,
      Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

/-- The decomposition of `P` obtained from decompositions of `P₁` and `P₂` and a presentation of
`P` as the direct sum of `P₁` and `P₂`. -/
def sum {P₁ P₂ : C} (D₁ : ShiftDecomposition E P₁) (D₂ : ShiftDecomposition E P₂)
    (i₁ : P₁ ⟶ P) (i₂ : P₂ ⟶ P) (p₁ : P ⟶ P₁) (p₂ : P ⟶ P₂)
    (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 P) (h₁ : i₁ ≫ p₁ = 𝟙 P₁) (h₂ : i₂ ≫ p₂ = 𝟙 P₂)
    (h₁₂ : i₁ ≫ p₂ = 0) (h₂₁ : i₂ ≫ p₁ = 0) : ShiftDecomposition E P where
  ι := D₁.ι ⊕ D₂.ι
  fintype := letI := D₁.fintype; letI := D₂.fintype; inferInstance
  decEq := letI := D₁.decEq; letI := D₂.decEq; inferInstance
  deg := Sum.elim D₁.deg D₂.deg
  incl
    | .inl j => D₁.incl j ≫ i₁
    | .inr j => D₂.incl j ≫ i₂
  proj
    | .inl j => p₁ ≫ D₁.proj j
    | .inr j => p₂ ≫ D₂.proj j
  total := by
    rw [Fintype.sum_sum_type]
    have e₁ : ∑ j, p₁ ≫ D₁.proj j ≫ D₁.incl j ≫ i₁ = p₁ ≫ i₁ := by
      calc _ = p₁ ≫ (∑ j, D₁.proj j ≫ D₁.incl j) ≫ i₁ := by
            simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
        _ = _ := by rw [D₁.total, Category.id_comp]
    have e₂ : ∑ j, p₂ ≫ D₂.proj j ≫ D₂.incl j ≫ i₂ = p₂ ≫ i₂ := by
      calc _ = p₂ ≫ (∑ j, D₂.proj j ≫ D₂.incl j) ≫ i₂ := by
            simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
        _ = _ := by rw [D₂.total, Category.id_comp]
    simp only [Category.assoc]
    rw [e₁, e₂, htot]
  incl_proj_self
    | .inl j => by simp [reassoc_of% h₁, D₁.incl_proj_self]
    | .inr j => by simp [reassoc_of% h₂, D₂.incl_proj_self]
  incl_proj_of_ne
    | .inl j, .inl j', h => by
        simp [reassoc_of% h₁, D₁.incl_proj_of_ne j j' (fun e ↦ h (congrArg _ e))]
    | .inl j, .inr j', _ => by simp [reassoc_of% h₁₂]
    | .inr j, .inl j', _ => by simp [reassoc_of% h₂₁]
    | .inr j, .inr j', h => by
        simp [reassoc_of% h₂, D₂.incl_proj_of_ne j j' (fun e ↦ h (congrArg _ e))]

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

/-- The image of a decomposition under an additive functor commuting with the shifts. -/
noncomputable def map (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] (Dc : ShiftDecomposition E P) :
    ShiftDecomposition (F.obj E) (F.obj P) where
  ι := Dc.ι
  deg := Dc.deg
  incl j := (F.commShiftIso (Dc.deg j)).inv.app E ≫ F.map (Dc.incl j)
  proj j := F.map (Dc.proj j) ≫ (F.commShiftIso (Dc.deg j)).hom.app E
  total := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← F.map_comp, ← F.map_sum, Dc.total,
      F.map_id]
  incl_proj_self j := by
    simp only [Category.assoc, ← F.map_comp_assoc, Dc.incl_proj_self, F.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
    rfl
  incl_proj_of_ne j j' h := by
    simp only [Category.assoc, ← F.map_comp_assoc, Dc.incl_proj_of_ne j j' h, F.map_zero,
      Limits.zero_comp, Limits.comp_zero]

end ShiftDecomposition

end CategoryTheory
