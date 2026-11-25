/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Compactness with respect to a fixed family

An object `s` of a preadditive category is *compact for a family* `Y` with a coproduct
(`CategoryTheory.CompactFor`) if every morphism `s ⟶ ∐ Y` is a finite sum of morphisms through
the summands. We record how this property moves along families of morphisms which induce
bijections (or surjections) on morphisms out of `s`, and when such bijections come from
distinguished triangles whose third (or first) term receives no morphisms from `s`.

These are the formal steps of the truncation argument for compactness used in blueprint
`proposition-compactness-finite-coefficients--1`.
-/

@[expose] public section

open CategoryTheory Limits Category Preadditive Pretriangulated

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]

/-- An object `s` is compact for a family `Y` if every morphism `s ⟶ ∐ Y` is a finite sum of
morphisms through the summands. -/
def CompactFor (s : C) {J : Type*} (Y : J → C) [HasCoproduct Y] : Prop :=
  ∀ f : s ⟶ ∐ Y, ∃ (S : Finset J) (g : ∀ j, s ⟶ Y j), f = ∑ j ∈ S, g j ≫ Sigma.ι Y j

namespace CompactFor

variable {s : C} {J : Type*}

/-- Compactness for a family gives the decomposition for any coproduct cofan of the family. -/
lemma of_isColimit {Y : J → C} [HasCoproduct Y] (h : CompactFor s Y) {c : Cofan Y}
    (hc : IsColimit c) (f : s ⟶ c.pt) :
    ∃ (S : Finset J) (g : ∀ j, s ⟶ Y j), f = ∑ j ∈ S, g j ≫ c.inj j := by
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor Y))
  obtain ⟨S, g, hg⟩ := h (f ≫ e.hom)
  refine ⟨S, g, ?_⟩
  rw [← cancel_mono e.hom, hg, sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [assoc]
  exact congrArg _ (hc.comp_coconePointUniqueUpToIso_hom _ ⟨j⟩).symm

/-- If `φⱼ : Aⱼ ⟶ Yⱼ` is a family such that every morphism `s ⟶ ∐ Y` factors through
`∐ φ`, and `s` is compact for `A`, then `s` is compact for `Y`. -/
lemma of_surjective {A Y : J → C} [HasCoproduct A] [HasCoproduct Y] (φ : ∀ j, A j ⟶ Y j)
    (hA : CompactFor s A)
    (hφ : Function.Surjective fun f : s ⟶ ∐ A ↦ f ≫ Limits.Sigma.map φ) : CompactFor s Y := by
  intro f
  obtain ⟨f', rfl⟩ := hφ f
  obtain ⟨S, g, rfl⟩ := hA f'
  refine ⟨S, fun j ↦ g j ≫ φ j, ?_⟩
  simp [sum_comp]

/-- If `ψⱼ : Aⱼ ⟶ Tⱼ` is a family inducing bijections on morphisms out of `s`, both for each `j`
and for `∐ ψ`, and `s` is compact for `T`, then `s` is compact for `A`. -/
lemma of_bijective {A T : J → C} [HasCoproduct A] [HasCoproduct T] (ψ : ∀ j, A j ⟶ T j)
    (hT : CompactFor s T) (hψ : ∀ j, Function.Surjective fun f : s ⟶ A j ↦ f ≫ ψ j)
    (hψ' : Function.Injective fun f : s ⟶ ∐ A ↦ f ≫ Limits.Sigma.map ψ) : CompactFor s A := by
  intro f
  obtain ⟨S, g, hg⟩ := hT (f ≫ Limits.Sigma.map ψ)
  choose g' hg' using fun j ↦ hψ j (g j)
  refine ⟨S, g', hψ' ?_⟩
  dsimp only
  rw [hg, sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [← hg' j]

end CompactFor

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- For a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` and an object `s` with no nonzero
morphisms to `T₃` and to `T₃⟦-1⟧`, composition with `T₁ ⟶ T₂` is bijective on morphisms out
of `s`. -/
lemma bijective_comp_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (s : C)
    (h₃ : ∀ f : s ⟶ T.obj₃, f = 0) (h₃' : ∀ f : s ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0) :
    Function.Bijective fun f : s ⟶ T.obj₁ ↦ f ≫ T.mor₁ := by
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun f ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) (f₁ - f₂)
      (by simpa [sub_comp] using sub_eq_zero.2 hf)
    rw [hg, h₃' g, zero_comp]
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT f (h₃ _)
    exact ⟨g, hg.symm⟩

/-- For a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` and an object `s` with no nonzero
morphisms to `T₁` and to `T₁⟦1⟧`, composition with `T₂ ⟶ T₃` is bijective on morphisms out
of `s`. -/
lemma bijective_comp_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (s : C)
    (h₁ : ∀ f : s ⟶ T.obj₁, f = 0) (h₁' : ∀ f : s ⟶ T.obj₁⟦(1 : ℤ)⟧, f = 0) :
    Function.Bijective fun f : s ⟶ T.obj₂ ↦ f ≫ T.mor₂ := by
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun f ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT (f₁ - f₂)
      (by simpa [sub_comp] using sub_eq_zero.2 hf)
    rw [hg, h₁ g, zero_comp]
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT f (h₁' _)
    exact ⟨g, hg.symm⟩

end CategoryTheory
