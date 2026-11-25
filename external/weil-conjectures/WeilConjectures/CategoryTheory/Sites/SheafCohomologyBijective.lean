/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Bijectivity of maps on sheaf cohomology

Consequences of the long exact cohomology sequence: in a short exact sequence of abelian
sheaves, a term without cohomology in two consecutive degrees makes the other map bijective; a
morphism whose kernel and cokernel are acyclic induces bijections in degrees at least two.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Abelian Limits

section Bijective

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

include hS in
/-- In a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves with
`Hⁿ(S.X₁) = Hⁿ⁺¹(S.X₁) = 0`, the map `Hⁿ(S.X₂) → Hⁿ(S.X₃)` is bijective. -/
lemma Sheaf.H.bijective_map_g (n : ℕ) [Subsingleton (H S.X₁ n)]
    [Subsingleton (H S.X₁ (n + 1))] : Function.Bijective (H.map S.g n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x hx
    rw [Subsingleton.elim y 0, Ext.zero_comp]
  · exact Ext.covariant_sequence_exact₃ _ hS z rfl (Subsingleton.elim _ _)

include hS in
/-- In a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves with
`Hᵐ(S.X₃) = Hᵐ⁺¹(S.X₃) = 0`, the map `Hᵐ⁺¹(S.X₁) → Hᵐ⁺¹(S.X₂)` is bijective. -/
lemma Sheaf.H.bijective_map_f (m : ℕ) [Subsingleton (H S.X₃ m)]
    [Subsingleton (H S.X₃ (m + 1))] : Function.Bijective (H.map S.f (m + 1)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x hx rfl
    rw [Subsingleton.elim z 0, Ext.zero_comp]
  · exact Ext.covariant_sequence_exact₂ _ hS y (Subsingleton.elim _ _)

/-- A morphism `φ` of abelian sheaves whose kernel and cokernel have no cohomology in positive
degrees induces bijections `Hⁿ(F) → Hⁿ(G)` for `n ≥ 2`: factor `φ` through its image and use
the two long exact sequences. -/
lemma Sheaf.H.bijective_map_of_subsingleton {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    (hK : ∀ i, Subsingleton (H (kernel φ) (i + 1)))
    (hQ : ∀ i, Subsingleton (H (cokernel φ) (i + 1))) (n : ℕ) :
    Function.Bijective (H.map φ (n + 2)) := by
  let S₁ := ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ)
    (by rw [← cancel_mono (Abelian.image.ι φ), Category.assoc, Abelian.image.fac,
      kernel.condition, zero_comp])
  have hS₁ : S₁.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    refine ShortComplex.exact_of_f_is_kernel _ ?_
    refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk ↦ ⟨kernel.lift φ k ?_, kernel.lift_ι _ _ _⟩
    change k ≫ Abelian.factorThruImage φ = 0 at hk
    rw [← Abelian.image.fac φ, ← Category.assoc, hk, zero_comp]
  let S₂ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (by simp)
  have hS₂ : S₂.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      inferInstance inferInstance
  have h₁ : Function.Bijective (H.map S₁.g (n + 2)) :=
    have := hK (n + 1)
    have := hK (n + 2)
    H.bijective_map_g hS₁ (n + 2)
  have h₂ : Function.Bijective (H.map S₂.f (n + 2)) :=
    have := hQ n
    have := hQ (n + 1)
    H.bijective_map_f hS₂ (n + 1)
  convert h₂.comp h₁ using 1
  ext x
  change _ = H.map (Abelian.image.ι φ) _ (H.map (Abelian.factorThruImage φ) _ x)
  rw [← H.map_comp_apply, Abelian.image.fac]

end Bijective

end CategoryTheory
