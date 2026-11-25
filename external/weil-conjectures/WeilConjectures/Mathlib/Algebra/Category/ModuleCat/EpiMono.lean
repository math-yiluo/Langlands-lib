/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Elements outside the range of a linear map

Criteria for an element to stay outside the range of a linear map, transported along commuting
squares of modules, and the transport of membership in a supremum of ranges along isomorphisms.
-/

@[expose] public section

namespace ModuleCat

open CategoryTheory

/-- On modules: if `b` sends `y` outside the range of `bc₂`, and `bc₂` and `bc₁` are related by
isomorphisms `τ` and `σ`, then `b ≫ τ` sends `y` outside the range of `bc₁`. -/
lemma notMem_range_of_isIso_comm
    {R : Type*} [Ring R] {M₂ M₂' S₂ S₁ M₁ : ModuleCat R}
    (b : M₂ ⟶ M₂') (τ : M₂' ⟶ M₁) (bc₂ : S₂ ⟶ M₂') (σ : S₂ ⟶ S₁) (bc₁ : S₁ ⟶ M₁)
    [IsIso τ] [IsIso σ] (w : bc₂ ≫ τ = σ ≫ bc₁) (y : M₂) (hB : b.hom y ∉ Set.range bc₂.hom) :
    τ.hom (b.hom y) ∉ Set.range bc₁.hom := by
  rintro ⟨s, hs⟩
  apply hB
  refine ⟨(inv σ).hom s, ((ConcreteCategory.isIso_iff_bijective τ).1 inferInstance).1 ?_⟩
  rw [← hs, ← ModuleCat.comp_apply, w, ModuleCat.comp_apply, ← ModuleCat.comp_apply (inv σ),
    IsIso.inv_hom_id, ModuleCat.id_apply]

/-- On modules: if `b ≫ jι` sends `y` outside the range of `bcJ`, `jι ≫ τJ = τ ≫ ι₁` with `τJ`
injective and `bc₁ ≫ ι₁ = 0`, then `b ≫ τ` sends `y` outside the range of `bc₁`. -/
lemma notMem_range_of_mono_comm
    {R : Type*} [Ring R] {M₂ M₂' M₁ M₁' J₂ S₁ SJ : ModuleCat R}
    (b : M₂ ⟶ M₂') (τ : M₂' ⟶ M₁) (ι₁ : M₁ ⟶ M₁') (jι : M₂' ⟶ J₂) (τJ : J₂ ⟶ M₁')
    (bc₁ : S₁ ⟶ M₁) (bcJ : SJ ⟶ J₂) [Mono τJ] (wn : jι ≫ τJ = τ ≫ ι₁) (hz : bc₁ ≫ ι₁ = 0)
    (y : M₂) (hA : jι.hom (b.hom y) ∉ Set.range bcJ.hom) :
    τ.hom (b.hom y) ∉ Set.range bc₁.hom := by
  rintro ⟨s, hs⟩
  apply hA
  refine ⟨0, ?_⟩
  rw [map_zero]
  symm
  apply (ModuleCat.mono_iff_injective τJ).1 inferInstance
  rw [map_zero, ← ModuleCat.comp_apply, wn, ModuleCat.comp_apply, ← hs, ← ModuleCat.comp_apply,
    hz]
  rfl

/-- Transport of membership in a supremum of ranges along compatible isomorphisms. -/
lemma mem_iSup_range_of_comm
    {R : Type*} [Ring R] {ι : Type*} {A B : ι → ModuleCat R}
    {Al Bl : ModuleCat R} (s : ∀ i, A i ⟶ Al) (t : ∀ i, B i ⟶ Bl) (θ : ∀ i, A i ⟶ B i)
    [∀ i, IsIso (θ i)] (θl : Al ≅ Bl) (w : ∀ i, s i ≫ θl.hom = θ i ≫ t i) (y : Al)
    (hy : θl.hom.hom y ∈ ⨆ i, LinearMap.range (t i).hom) :
    y ∈ ⨆ i, LinearMap.range (s i).hom := by
  suffices H : ∀ z ∈ ⨆ i, LinearMap.range (t i).hom,
      θl.inv.hom z ∈ ⨆ i, LinearMap.range (s i).hom by
    simpa [← ModuleCat.comp_apply] using H _ hy
  intro z hz
  induction hz using Submodule.iSup_induction' with
  | mem i z hz =>
    obtain ⟨b, rfl⟩ := hz
    refine Submodule.mem_iSup_of_mem i ⟨(inv (θ i)).hom b, ?_⟩
    have hc : inv (θ i) ≫ s i = t i ≫ θl.inv := by
      rw [← cancel_mono θl.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, w,
        IsIso.inv_hom_id_assoc]
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hc]
  | zero => simp
  | add z₁ z₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂

end ModuleCat
