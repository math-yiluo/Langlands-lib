/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Cokernels of morphisms between finite biproducts of copies of an object

Let `C` be a preadditive category with finite biproducts and cokernels, and `R` an object of `C`
whose nonzero endomorphisms are isomorphisms (for instance the unit of the category of
modules over a field). Then the cokernel of any morphism `⨁_κ R ⟶ ⨁_ι R` between finite
biproducts of copies of `R` is again a finite biproduct of copies of `R`
(`CategoryTheory.Limits.exists_iso_biproduct_cokernel`). This is Gaussian elimination: a
morphism `R ⟶ ⨁_ι R` with a nonzero, hence invertible, component `i` is, up to an automorphism
of the target, the inclusion of the summand `i`, whose cokernel is the biproduct of the
remaining summands (`CategoryTheory.Limits.cokernelIsoOfIsIsoCompπ`); the cokernel of a
morphism out of a biproduct is computed one summand at a time
(`CategoryTheory.Limits.cokernelIsoCokernelFromSubtype`).
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

open Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [HasCokernels C]

section Subtype

variable {κ : Type} [Finite κ] (X : κ → C) {M : C} (f : ⨁ X ⟶ M) (i : κ)

/-- The morphism `⨁_{j ≠ i} X j ⟶ coker (f ∘ ιᵢ)` induced by a morphism `f : ⨁ X ⟶ M`. -/
noncomputable abbrev fromSubtypeCokernel :
    ⨁ Subtype.restrict (fun j ↦ j ≠ i) X ⟶ cokernel (biproduct.ι X i ≫ f) :=
  biproduct.fromSubtype X (fun j ↦ j ≠ i) ≫ f ≫ cokernel.π (biproduct.ι X i ≫ f)

lemma comp_cokernel_π_comp_cokernel_π :
    f ≫ cokernel.π (biproduct.ι X i ≫ f) ≫ cokernel.π (fromSubtypeCokernel X f i) = 0 := by
  refine biproduct.hom_ext' _ _ fun j ↦ ?_
  rw [comp_zero]
  by_cases hj : j = i
  · subst hj
    simp only [← Category.assoc]
    rw [cokernel.condition, zero_comp]
  · have h := biproduct.ι (Subtype.restrict (fun j ↦ j ≠ i) X) ⟨j, hj⟩ ≫=
      cokernel.condition (fromSubtypeCokernel X f i)
    rw [comp_zero, fromSubtypeCokernel, Category.assoc, Category.assoc,
      biproduct.ι_fromSubtype_assoc] at h
    simpa using h

/-- The cokernel of a morphism `f : ⨁ X ⟶ M` out of a finite biproduct, computed in two steps:
first the cokernel of the summand `i`, then the cokernel of the remaining summands. -/
noncomputable def isColimitCokernelCoforkFromSubtype :
    IsColimit (CokernelCofork.ofπ _ (comp_cokernel_π_comp_cokernel_π X f i)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun k hk ↦ cokernel.desc _ (cokernel.desc _ k (by rw [Category.assoc, hk, comp_zero]))
      (by rw [Category.assoc, Category.assoc, cokernel.π_desc, hk, comp_zero]))
    (fun k hk ↦ by simp)
    (fun k hk m hm ↦ by
      refine coequalizer.hom_ext (coequalizer.hom_ext ?_)
      simpa using hm)

/-- The cokernel of a morphism `f : ⨁ X ⟶ M` out of a finite biproduct is the cokernel of the
induced morphism `⨁_{j ≠ i} X j ⟶ coker (f ∘ ιᵢ)`. -/
noncomputable def cokernelIsoCokernelFromSubtype :
    cokernel f ≅ cokernel (fromSubtypeCokernel X f i) :=
  (cokernelIsCokernel f).coconePointUniqueUpToIso (isColimitCokernelCoforkFromSubtype X f i)

end Subtype

section Shear

omit [HasFiniteBiproducts C] [HasCokernels C] in
/-- If `a ≫ p = 0`, then `𝟙 + p ≫ a` is an isomorphism, with inverse `𝟙 - p ≫ a`. -/
lemma isIso_id_add_comp_of_comp_eq_zero {A B : C} (p : A ⟶ B) (a : B ⟶ A) (h : a ≫ p = 0) :
    IsIso (𝟙 A + p ≫ a) := by
  refine ⟨𝟙 A - p ≫ a, ?_, ?_⟩
  · simp [comp_sub, reassoc_of% h]
  · simp [sub_comp, reassoc_of% h]

variable {ι : Type} [Finite ι] (X : ι → C) {Y : C} (g : Y ⟶ ⨁ X) (i : ι)
  [IsIso (g ≫ biproduct.π X i)]

/-- The shear automorphism `𝟙 + πᵢ ≫ (ιᵢ - u⁻¹ ≫ g)` of `⨁ X`, for `u = g ≫ πᵢ` invertible,
which carries `g` to `u ≫ ιᵢ`. -/
noncomputable def shear : ⨁ X ⟶ ⨁ X :=
  𝟙 _ + biproduct.π X i ≫ (biproduct.ι X i - inv (g ≫ biproduct.π X i) ≫ g)

instance : IsIso (shear X g i) :=
  isIso_id_add_comp_of_comp_eq_zero _ _ (by
    rw [sub_comp, biproduct.ι_π_self, Category.assoc, IsIso.inv_hom_id, sub_self])

omit [HasCokernels C] in
lemma comp_shear : g ≫ shear X g i = (g ≫ biproduct.π X i) ≫ biproduct.ι X i := by
  simp only [shear, comp_add, Category.comp_id, comp_sub, ← Category.assoc, IsIso.hom_inv_id,
    Category.id_comp]
  abel

/-- **Gaussian elimination step**: if the component `g ≫ πᵢ` of `g : Y ⟶ ⨁ X` is invertible,
then the cokernel of `g` is the biproduct of the summands other than `i`. -/
noncomputable def cokernelIsoOfIsIsoCompπ :
    cokernel g ≅ ⨁ Subtype.restrict (fun j ↦ j ≠ i) X :=
  (cokernelCompIsIso g (shear X g i)).symm ≪≫ cokernelIsoOfEq (comp_shear X g i) ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelBiproductιIso X i

end Shear

section Division

variable (R : C)

/-- The objects isomorphic to a finite biproduct of copies of `R`. -/
def IsFiniteBiproductOf (M : C) : Prop :=
  ∃ (ι : Type) (_ : Finite ι), Nonempty (M ≅ ⨁ fun _ : ι ↦ R)

variable {R}

omit [HasCokernels C] in
lemma IsFiniteBiproductOf.of_iso {M N : C} (e : M ≅ N) (h : IsFiniteBiproductOf R M) :
    IsFiniteBiproductOf R N := by
  obtain ⟨ι, _, ⟨e'⟩⟩ := h
  exact ⟨ι, inferInstance, ⟨e.symm ≪≫ e'⟩⟩

/-- If the nonzero endomorphisms of `R` are isomorphisms, the cokernel of a morphism from `R` to
a finite biproduct of copies of `R` is a finite biproduct of copies of `R`. -/
lemma IsFiniteBiproductOf.cokernel_of_isIso (hR : ∀ g : R ⟶ R, g ≠ 0 → IsIso g) {M : C}
    (hM : IsFiniteBiproductOf R M) (g : R ⟶ M) : IsFiniteBiproductOf R (cokernel g) := by
  obtain ⟨ι, _, ⟨e⟩⟩ := hM
  refine IsFiniteBiproductOf.of_iso (cokernelCompIsIso g e.hom) ?_
  by_cases h : g ≫ e.hom = 0
  · exact ⟨ι, inferInstance, ⟨cokernelIsoOfEq h ≪≫ cokernelZeroIsoTarget⟩⟩
  · obtain ⟨i, hi⟩ : ∃ i, g ≫ e.hom ≫ biproduct.π _ i ≠ 0 := by
      by_contra! h'
      exact h (biproduct.hom_ext _ _ fun i ↦ by simpa using h' i)
    have : IsIso ((g ≫ e.hom) ≫ biproduct.π _ i) := hR _ (by simpa using hi)
    exact ⟨{ j // j ≠ i }, inferInstance, ⟨cokernelIsoOfIsIsoCompπ _ (g ≫ e.hom) i⟩⟩

/-- If the nonzero endomorphisms of `R` are isomorphisms, the cokernel of a morphism from a
finite biproduct of copies of `R` to a finite biproduct of copies of `R` is a finite biproduct
of copies of `R`. -/
lemma IsFiniteBiproductOf.cokernel_of_card_eq (hR : ∀ g : R ⟶ R, g ≠ 0 → IsIso g) :
    ∀ (n : ℕ) (κ : Type) [Finite κ], Nat.card κ = n → ∀ {M : C}, IsFiniteBiproductOf R M →
      ∀ f : (⨁ fun _ : κ ↦ R) ⟶ M, IsFiniteBiproductOf R (cokernel f) := by
  intro n
  induction n with
  | zero =>
    intro κ _ hκ M hM f
    have : IsEmpty κ := (Finite.card_eq_zero_iff).1 hκ
    have hf : f = 0 := biproduct.hom_ext' _ _ fun j ↦ isEmptyElim j
    exact IsFiniteBiproductOf.of_iso (cokernelIsoOfEq hf ≪≫ cokernelZeroIsoTarget).symm hM
  | succ n ih =>
    intro κ _ hκ M hM f
    have : Nonempty κ := (Finite.card_pos_iff).1 (by omega)
    obtain ⟨i⟩ := this
    refine IsFiniteBiproductOf.of_iso (cokernelIsoCokernelFromSubtype _ f i).symm ?_
    refine ih { j // j ≠ i } ?_ (hM.cokernel_of_isIso hR _) _
    classical
    have := Fintype.ofFinite κ
    rw [Nat.card_eq_fintype_card] at hκ ⊢
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hκ, Nat.add_sub_cancel]

/-- **Cokernels of matrices over a division ring**: if the nonzero endomorphisms of `R` are
isomorphisms, the cokernel of a morphism `⨁_κ R ⟶ ⨁_ι R` between finite biproducts of copies of
`R` is a finite biproduct of copies of `R`. -/
theorem isFiniteBiproductOf_cokernel (hR : ∀ g : R ⟶ R, g ≠ 0 → IsIso g) {κ ι : Type} [Finite κ]
    [Finite ι] (f : (⨁ fun _ : κ ↦ R) ⟶ ⨁ fun _ : ι ↦ R) : IsFiniteBiproductOf R (cokernel f) :=
  IsFiniteBiproductOf.cokernel_of_card_eq hR _ κ rfl ⟨ι, inferInstance, ⟨Iso.refl _⟩⟩ f

end Division

end CategoryTheory.Limits
