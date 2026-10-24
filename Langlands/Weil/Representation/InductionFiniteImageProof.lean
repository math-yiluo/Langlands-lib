/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Worker 261

The quotient-lift construction of `identityCosetProjection` is adapted from
Mathlib's `Rep.indResHomEquiv`.
-/
import Langlands.Weil.Representation.InductionFinitenessStatements

/-!
# Finite whole image under finite-index induction

The induced action is Mathlib's actual `Representation.ind` on the coinvariant
space `Representation.IndV`. If `ρ` has finite image, the normal core of its
kernel has finite index in `G` and acts trivially on the induced space. Conversely,
`ρ` is the compression of the induced action to the identity-coset copy of `V`.
-/

noncomputable section

namespace Langlands.Weil

open Representation

universe uG uV

section

variable {G : Type uG} [Group G] (H : Subgroup G)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

open scoped Classical in
/-- The identity-coset projection, sending `⟦g ⊗ v⟧` to `ρ(g⁻¹) v` when `g ∈ H`
and to `0` otherwise. -/
private def identityCosetProjection : IndV H.subtype ρ →ₗ[ℂ] V :=
  Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun g : G =>
        if hg : g ∈ H then ρ (⟨g, hg⟩ : H)⁻¹ else 0) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)
    (fun s => by
      ext g v
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single]
      by_cases hg : g ∈ H
      · rw [dite_eq_left (H.mul_mem s.2 hg), dite_eq_left hg, ← Module.End.mul_apply, ← map_mul]
        congr 2
        apply Subtype.ext
        simp [mul_assoc]
      · rw [dite_eq_right (fun h => hg ((H.mul_mem_cancel_left s.2).mp h)), dite_eq_right hg]
        simp)

open scoped Classical in
private theorem identityCosetProjection_mk (g : G) (v : V) :
    identityCosetProjection H ρ (IndV.mk H.subtype ρ g v) =
      if hg : g ∈ H then ρ (⟨g, hg⟩ : H)⁻¹ v else 0 := by
  by_cases hg : g ∈ H <;> simp [identityCosetProjection, hg]

/-- Compressing the induced action of `s ∈ H` to the identity-coset copy of `V`
recovers `ρ s`. -/
private theorem compress_ind (s : H) :
    identityCosetProjection H ρ ∘ₗ ρ.ind H.subtype (s : G) ∘ₗ IndV.mk H.subtype ρ 1 =
      ρ s := by
  apply LinearMap.ext
  intro v
  change identityCosetProjection H ρ (ρ.ind H.subtype (s : G) (IndV.mk H.subtype ρ 1 v)) =
    ρ s v
  rw [ind_mk, one_mul, identityCosetProjection_mk, dite_eq_left (H.inv_mem s.2),
    show (⟨(s : G)⁻¹, H.inv_mem s.2⟩ : H)⁻¹ = s from Subtype.ext (by simp)]

/-- Reflection: finite whole image of the induced action gives finite image of `ρ`. -/
private theorem finite_range_of_finite_range_ind
    (h : (Set.range (ρ.ind H.subtype)).Finite) : (Set.range ρ).Finite := by
  refine (h.image fun A => identityCosetProjection H ρ ∘ₗ A ∘ₗ IndV.mk H.subtype ρ 1).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨_, ⟨(s : G), rfl⟩, compress_ind H ρ s⟩

/-- Every element of the normal core of the kernel of `ρ`, viewed in `G`, acts
trivially on the induced space. -/
private theorem ind_eq_one_of_mem_normalCore (g : G)
    (hg : g ∈ (ρ.ker.map H.subtype).normalCore) : ρ.ind H.subtype g = 1 := by
  apply IndV.hom_ext
  intro x
  apply LinearMap.ext
  intro v
  change ρ.ind H.subtype g (IndV.mk H.subtype ρ x v) = IndV.mk H.subtype ρ x v
  rw [ind_mk]
  obtain ⟨k, hk, hkx⟩ := (Subgroup.normalCore (ρ.ker.map H.subtype)).inv_mem hg x
  have hx : x * g⁻¹ = (k : G) * x := by
    rw [Subgroup.coe_subtype] at hkx
    rw [hkx]
    group
  rw [hx]
  have hρk : ρ k = 1 := hk
  calc IndV.mk H.subtype ρ ((k : G) * x) v
      = IndV.mk H.subtype ρ ((k : G) * x) (ρ k v) := by rw [hρk]; rfl
    _ = IndV.mk H.subtype ρ x v := by
      refine Eq.trans ?_ (Coinvariants.mk_self_apply _ k (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] v))
      simp [ofMulAction_single]

/-- A representation with finite image has a finite-index kernel. -/
private theorem finiteIndex_ker_of_finite_range (h : (Set.range ρ).Finite) :
    ρ.ker.FiniteIndex := by
  have hker : ρ.toHomUnits.ker = ρ.ker := by
    ext s
    simp [MonoidHom.mem_ker]
  have hfin : (Set.range ρ.toHomUnits).Finite :=
    (h.preimage Units.val_injective.injOn).subset (by
      rintro _ ⟨s, rfl⟩
      exact ⟨s, rfl⟩)
  have : Finite ρ.toHomUnits.range := by
    rw [← MonoidHom.coe_range] at hfin
    exact hfin.to_subtype
  rw [← hker]
  infer_instance

/-- Preservation: finite image of `ρ` gives finite whole image of the induced action. -/
private theorem finite_range_ind_of_finite_range [H.FiniteIndex]
    (h : (Set.range ρ).Finite) : (Set.range (ρ.ind H.subtype)).Finite := by
  have := finiteIndex_ker_of_finite_range H ρ h
  have : (ρ.ker.map H.subtype).FiniteIndex :=
    ⟨by
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  have hN : (ρ.ker.map H.subtype).normalCore ≤ (ρ.ind H.subtype).ker :=
    fun g hg => ind_eq_one_of_mem_normalCore H ρ g hg
  refine (Set.finite_range (QuotientGroup.lift _ (ρ.ind H.subtype) hN)).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨(g : G ⧸ (ρ.ker.map H.subtype).normalCore), rfl⟩

end

/-- Finite-index induction preserves and reflects finite whole image. -/
theorem representationInductionFiniteImage :
    RepresentationInductionFiniteImage.{uG, uV} := by
  intro G _ H _ V _ _ _ ρ
  exact ⟨finite_range_of_finite_range_ind H ρ, finite_range_ind_of_finite_range H ρ⟩

-- Check the complete unapplied constant, preserving both universe parameters.
example : RepresentationInductionFiniteImage.{uG, uV} :=
  @representationInductionFiniteImage.{uG, uV}

end Langlands.Weil
