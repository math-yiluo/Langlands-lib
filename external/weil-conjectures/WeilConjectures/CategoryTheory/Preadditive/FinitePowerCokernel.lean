/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Cokernels of morphisms between finite powers of an object with a division endomorphism ring

Let `C` be a preadditive category with finite biproducts and cokernels, and `U` an object of `C`
whose nonzero endomorphisms are all invertible, so that `End U` is a division ring. Then the
cokernel of any morphism `Uᵐ ⟶ Uⁿ` between finite biproducts of copies of `U` is again a finite
biproduct of copies of `U` (`CategoryTheory.Limits.exists_iso_biproduct_cokernel`): this is the
categorical form of the rank normal form of a matrix over a division ring.

We also record that "nonzero endomorphisms are invertible" and `𝟙 ≠ 0` transfer along full,
respectively faithful, functors preserving zero morphisms
(`CategoryTheory.Functor.isIso_of_ne_zero_end`,
`CategoryTheory.Functor.one_ne_zero_end`) and along surjective ring homomorphisms from a field
(`CategoryTheory.isIso_of_ne_zero_of_surjective`).

## Main results

- `CategoryTheory.Limits.biproductFinSuccIso`: `⨁ f ≅ f 0 ⊞ ⨁ (f ∘ Fin.succ)`.
- `CategoryTheory.Limits.exists_iso_biproduct_cokernel`: cokernels of morphisms between finite
  powers of `U` are finite powers of `U`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

/-! ### Transferring the field property of an endomorphism ring -/

/-- If a ring homomorphism from a field onto `End X` is surjective, every nonzero endomorphism
of `X` is invertible. -/
lemma isIso_of_ne_zero_of_surjective {C : Type u} [Category.{v} C] [Preadditive C] {X : C}
    {K : Type*} [Field K] (φ : K →+* End X) (hφ : Function.Surjective φ) (t : End X)
    (ht : t ≠ 0) : IsIso (t).asHom := by
  obtain ⟨a, rfl⟩ := hφ t
  have ha : a ≠ 0 := by
    rintro rfl
    exact ht (map_zero φ)
  exact (isUnit_iff_isIso _).1 ((Ne.isUnit ha).map φ)

/-- Let `F` be a full functor preserving zero morphisms and `F X ≅ Y`. If every nonzero
endomorphism of `X` is invertible, so is every nonzero endomorphism of `Y`. -/
lemma Functor.isIso_of_ne_zero_end {C : Type*} [Category* C] {D : Type*} [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Full]
    [F.PreservesZeroMorphisms] {X : C} {Y : D} (e : F.obj X ≅ Y)
    (h : ∀ t : End X, t ≠ 0 → IsIso (t).asHom) (t : End Y) (ht : t ≠ 0) : IsIso (t).asHom := by
  obtain ⟨s, hs⟩ := F.map_surjective (e.hom ≫ t.asHom ≫ e.inv)
  have hs' : t.asHom = e.inv ≫ F.map s ≫ e.hom := by
    simp [hs]
  have : IsIso s := h (.of s) (by
    intro hs0
    apply ht
    apply End.ext
    have hs0' : s = 0 := by simpa only [End.zero_asHom] using congr($(hs0).asHom)
    rw [hs', hs0', F.map_zero, Limits.zero_comp, Limits.comp_zero, End.zero_asHom])
  rw [hs']
  infer_instance

/-- Let `F` be a faithful functor preserving zero morphisms and `F X ≅ Y`. If `𝟙 X ≠ 0`, then
`𝟙 Y ≠ 0`. -/
lemma Functor.one_ne_zero_end {C : Type*} [Category* C] {D : Type*} [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Faithful]
    [F.PreservesZeroMorphisms] {X : C} {Y : D} (e : F.obj X ≅ Y) (h : (1 : End X) ≠ 0) :
    (1 : End Y) ≠ 0 := by
  intro h'
  apply h
  apply End.ext
  apply F.map_injective
  have h'' : 𝟙 Y = 0 := congr($(h').asHom)
  rw [End.zero_asHom, End.one_asHom, F.map_zero, F.map_id, ← e.hom_inv_id,
    ← Category.id_comp e.inv, h'', Limits.zero_comp, Limits.comp_zero]

namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### Splitting off the first summand of a biproduct indexed by `Fin (n + 1)` -/

/-- A biproduct indexed by `Fin (n + 1)` is the binary biproduct of its first summand and of the
biproduct of the remaining ones. -/
noncomputable def biproductFinSuccIso {n : ℕ} (f : Fin (n + 1) → C) [HasBiproduct f]
    [HasBiproduct fun i : Fin n ↦ f i.succ]
    [HasBinaryBiproduct (f 0) (⨁ fun i : Fin n ↦ f i.succ)] :
    ⨁ f ≅ f 0 ⊞ ⨁ fun i : Fin n ↦ f i.succ where
  hom := biprod.lift (biproduct.π f 0) (biproduct.lift fun i ↦ biproduct.π f i.succ)
  inv := biprod.desc (biproduct.ι f 0) (biproduct.desc fun i ↦ biproduct.ι f i.succ)
  hom_inv_id := by
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    rw [Category.comp_id]
    induction j using Fin.cases with
    | zero =>
      have : (biproduct.ι f 0 ≫ biproduct.lift fun i : Fin n ↦ biproduct.π f i.succ) = 0 :=
        biproduct.hom_ext _ _ fun (i : Fin n) ↦ by
          rw [Category.assoc, biproduct.lift_π, biproduct.ι_π_ne _ (Fin.succ_ne_zero i).symm,
            zero_comp]
      rw [biprod.lift_desc, Preadditive.comp_add, biproduct.ι_π_self_assoc, reassoc_of% this,
        zero_comp, add_zero]
    | succ j =>
      have : (biproduct.ι f j.succ ≫ biproduct.lift fun i : Fin n ↦ biproduct.π f i.succ) =
          biproduct.ι (fun i : Fin n ↦ f i.succ) j :=
        biproduct.hom_ext _ _ fun (i : Fin n) ↦ by
          rw [Category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π]
          by_cases h : j = i
          · subst h
            simp
          · rw [dite_eq_right h, dite_eq_right ((Fin.succ_injective _).ne h)]
      rw [biprod.lift_desc, Preadditive.comp_add, biproduct.ι_π_ne_assoc _ (Fin.succ_ne_zero j),
        zero_comp, zero_add, reassoc_of% this, biproduct.ι_desc]
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biproduct.ι_π_self, biprod.inl_fst]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        exact biproduct.hom_ext _ _ fun (i : Fin n) ↦ by
          rw [Category.assoc, biproduct.lift_π, biproduct.ι_π_ne _ (Fin.succ_ne_zero i).symm,
            zero_comp]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
        exact biproduct.hom_ext' _ _ fun (i : Fin n) ↦ by
          rw [biproduct.ι_desc_assoc, biproduct.ι_π_ne _ (Fin.succ_ne_zero i), comp_zero]
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        refine biproduct.hom_ext' _ _ fun i ↦ biproduct.hom_ext _ _ fun k ↦ ?_
        rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
          biproduct.ι_π, biproduct.ι_π]
        by_cases h : i = k
        · subst h
          simp
        · rw [dite_eq_right h, dite_eq_right ((Fin.succ_injective _).ne h)]

/-- A biproduct indexed by `Fin 0` is zero. -/
lemma isZero_biproduct_fin_zero (f : Fin 0 → C) [HasBiproduct f] : IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext' _ _ fun i ↦ i.elim0

/-! ### Some cokernels of morphisms into and out of binary biproducts -/

/-- The cokernel of `(a, b) : U ⟶ A ⊞ B` with `a` invertible is `B`. -/
noncomputable def isColimitCokernelCoforkBiprodLiftOfIsIso {U A B : C} [HasBinaryBiproduct A B]
    (a : U ⟶ A) [IsIso a] (b : U ⟶ B) :
    IsColimit (CokernelCofork.ofπ (f := biprod.lift a b) (biprod.desc (-(inv a ≫ b)) (𝟙 B))
      (by simp)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun g' _ ↦ biprod.inr ≫ g')
    (fun g' hg' ↦ by
      have h : a ≫ biprod.inl ≫ g' = -(b ≫ biprod.inr ≫ g') := by
        rw [biprod.lift_eq, Preadditive.add_comp, Category.assoc, Category.assoc] at hg'
        exact eq_neg_of_add_eq_zero_left hg'
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, Preadditive.neg_comp, Category.assoc, ← Preadditive.comp_neg,
          ← h, IsIso.inv_hom_id_assoc]
      · rw [biprod.inr_desc_assoc, Category.id_comp])
    (fun g' _ m hm ↦ by
      rw [← hm, biprod.inr_desc_assoc, Category.id_comp])

/-- The cokernel of `(0, b) : U ⟶ A ⊞ B` is `A ⊞ coker b`. -/
noncomputable def isColimitCokernelCoforkBiprodLiftZero {U A B : C} [HasBinaryBiproduct A B]
    (b : U ⟶ B) [HasCokernel b] [HasBinaryBiproduct A (cokernel b)] :
    IsColimit (CokernelCofork.ofπ (f := biprod.lift 0 b) (biprod.map (𝟙 A) (cokernel.π b))
      (by apply biprod.hom_ext <;> simp)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g' hg' ↦ biprod.desc (biprod.inl ≫ g') (cokernel.desc b (biprod.inr ≫ g') (by
      rw [biprod.lift_eq, zero_comp, zero_add, Category.assoc] at hg'
      exact hg')))
    (fun g' hg' ↦ by
      apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc]
      · rw [biprod.inr_map_assoc, biprod.inr_desc, cokernel.π_desc])
    (fun g' _ m hm ↦ by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc, ← hm, biprod.inl_map_assoc, Category.id_comp]
      · rw [biprod.inr_desc]
        refine coequalizer.hom_ext ?_
        rw [cokernel.π_desc, ← hm, biprod.inr_map_assoc])

/-- The cokernel of `[f₁, f₂] : A ⊞ B ⟶ X` is the cokernel of `B ⟶ X ⟶ coker f₁`. -/
noncomputable def isColimitCokernelCoforkBiprodDesc {A B X : C} [HasBinaryBiproduct A B]
    (f₁ : A ⟶ X) (f₂ : B ⟶ X) [HasCokernel f₁] [HasCokernel (f₂ ≫ cokernel.π f₁)] :
    IsColimit (CokernelCofork.ofπ (f := biprod.desc f₁ f₂)
      (cokernel.π f₁ ≫ cokernel.π (f₂ ≫ cokernel.π f₁)) (by
        apply biprod.hom_ext'
        · rw [biprod.inl_desc_assoc, cokernel.condition_assoc, zero_comp, comp_zero]
        · rw [biprod.inr_desc_assoc, ← Category.assoc, cokernel.condition, comp_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g' hg' ↦ cokernel.desc _ (cokernel.desc f₁ g' (by
      simpa using biprod.inl ≫= hg')) (by
      rw [Category.assoc, cokernel.π_desc]
      simpa using biprod.inr ≫= hg'))
    (fun g' hg' ↦ by simp)
    (fun g' _ m hm ↦ by
      refine coequalizer.hom_ext (coequalizer.hom_ext ?_)
      simpa using hm)


/-! ### Cokernels of morphisms between finite powers -/

section Power

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C] [HasCokernels C] {U : C}

/-- The cokernel of a morphism `U ⟶ Uⁿ` is a finite power of `U`, if every nonzero endomorphism
of `U` is invertible. -/
theorem exists_iso_biproduct_cokernel_of_source (hU : ∀ t : End U, t ≠ 0 → IsIso (t).asHom) {n : ℕ}
    {X : C} (eX : X ≅ ⨁ fun _ : Fin n ↦ U) (g : U ⟶ X) :
    ∃ k : ℕ, Nonempty (cokernel g ≅ ⨁ fun _ : Fin k ↦ U) := by
  induction n generalizing X with
  | zero =>
    exact ⟨0, ⟨IsZero.iso (IsZero.of_epi (cokernel.π g)
      ((isZero_biproduct_fin_zero _).of_iso eX)) (isZero_biproduct_fin_zero _)⟩⟩
  | succ n ih =>
    let e := eX ≪≫ biproductFinSuccIso fun _ : Fin (n + 1) ↦ U
    have hg : g ≫ e.hom = biprod.lift (g ≫ e.hom ≫ biprod.fst) (g ≫ e.hom ≫ biprod.snd) := by
      apply biprod.hom_ext <;> simp
    by_cases ha : (.of (g ≫ e.hom ≫ biprod.fst) : End U) = 0
    · obtain ⟨k, ⟨e'⟩⟩ := ih (Iso.refl _) (g ≫ e.hom ≫ biprod.snd)
      have ha' : g ≫ e.hom ≫ biprod.fst = 0 := by
        simpa only [End.zero_asHom] using congr($(ha).asHom)
      rw [ha'] at hg
      exact ⟨k + 1, ⟨(cokernelCompIsIso g e.hom).symm ≪≫ cokernelIsoOfEq hg ≪≫
        IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (isColimitCokernelCoforkBiprodLiftZero _) ≪≫
        biprod.mapIso (Iso.refl U) e' ≪≫ (biproductFinSuccIso fun _ : Fin (k + 1) ↦ U).symm⟩⟩
    · have : IsIso (g ≫ e.hom ≫ biprod.fst) := hU _ ha
      exact ⟨n, ⟨(cokernelCompIsIso g e.hom).symm ≪≫ cokernelIsoOfEq hg ≪≫
        IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (isColimitCokernelCoforkBiprodLiftOfIsIso _ _)⟩⟩

/-- **Cokernels of morphisms between finite powers.** If every nonzero endomorphism of `U` is
invertible, the cokernel of a morphism `Uᵐ ⟶ Uⁿ` between finite biproducts of copies of `U` is
again a finite biproduct of copies of `U`. -/
theorem exists_iso_biproduct_cokernel (hU : ∀ t : End U, t ≠ 0 → IsIso (t).asHom)
    {m n : ℕ} {X Y : C}
    (eY : Y ≅ ⨁ fun _ : Fin m ↦ U) (eX : X ≅ ⨁ fun _ : Fin n ↦ U) (f : Y ⟶ X) :
    ∃ k : ℕ, Nonempty (cokernel f ≅ ⨁ fun _ : Fin k ↦ U) := by
  induction m generalizing n X Y with
  | zero =>
    obtain rfl : f = 0 := ((isZero_biproduct_fin_zero _).of_iso eY).eq_of_src _ _
    exact ⟨n, ⟨cokernelZeroIsoTarget ≪≫ eX⟩⟩
  | succ m ih =>
    let e := eY ≪≫ biproductFinSuccIso fun _ : Fin (m + 1) ↦ U
    have hf : e.inv ≫ f = biprod.desc (biprod.inl ≫ e.inv ≫ f) (biprod.inr ≫ e.inv ≫ f) := by
      apply biprod.hom_ext' <;> simp
    obtain ⟨k, ⟨e₁⟩⟩ := exists_iso_biproduct_cokernel_of_source hU eX (biprod.inl ≫ e.inv ≫ f)
    obtain ⟨j, ⟨e₂⟩⟩ := ih (Iso.refl _) e₁
      ((biprod.inr ≫ e.inv ≫ f) ≫ cokernel.π (biprod.inl ≫ e.inv ≫ f))
    exact ⟨j, ⟨(cokernelEpiComp e.inv f).symm ≪≫ cokernelIsoOfEq hf ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitCokernelCoforkBiprodDesc _ _) ≪≫ e₂⟩⟩

end Power

end Limits

end CategoryTheory
