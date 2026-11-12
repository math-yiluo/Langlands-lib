/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Kernel cosets and saturated cosets

Modified by Worker 120: extract M006.006 from the pinned NYLL `Indices.lean`,
prefix the namespace, and place the original private construction and its
well-definedness and bijectivity arguments inside the data definition.
See the paired Markdown for source correspondence and modification details.
-/

namespace Langlands.NYLL.ClassFormation

universe u v

variable {G : Type u} {D : Type v} [Group G] [Group D]

/-- The kernel cosets for `L ≤ K` are the cosets in the part of `K` saturated by
`ker d`. This is an equivalence of coset types; `L` need not be normal. -/
noncomputable def kernelCosetEquivSaturation (d : G →* D) {L K : Subgroup G}
    (hLK : L ≤ K) :
    (↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) ≃
      (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))) := by
  let kernelToSaturation (d : G →* D) (L K : Subgroup G) :
      ↑(K ⊓ d.ker) →* ↑(K ⊓ (L ⊔ d.ker)) :=
    Subgroup.inclusion (inf_le_inf le_rfl le_sup_right)
  have kernelToSaturation_rel_iff (d : G →* D) (L K : Subgroup G)
      (x y : ↑(K ⊓ d.ker)) :
      QuotientGroup.leftRel ((L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) x y ↔
        QuotientGroup.leftRel (L.subgroupOf (K ⊓ (L ⊔ d.ker)))
          (kernelToSaturation d L K x) (kernelToSaturation d L K y) := by
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · exact fun h ↦ h.1
    · intro h
      exact ⟨h, d.ker.mul_mem (d.ker.inv_mem x.property.2) y.property.2⟩
  let kernelCosetToSaturationCoset (d : G →* D) (L K : Subgroup G) :
      (↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) →
        (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))) :=
    Quotient.map' (kernelToSaturation d L K) fun x y h ↦
      (kernelToSaturation_rel_iff d L K x y).mp h
  have kernelCosetToSaturationCoset_injective (d : G →* D) (L K : Subgroup G) :
      Function.Injective (kernelCosetToSaturationCoset d L K) := by
    intro q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro x y h
    apply Quotient.eq''.mpr
    apply (kernelToSaturation_rel_iff d L K x y).mpr
    apply Quotient.eq''.mp
    simpa only [kernelCosetToSaturationCoset, Quotient.map'_mk''] using h
  have kernelCosetToSaturationCoset_surjective (d : G →* D) {L K : Subgroup G}
      (hLK : L ≤ K) : Function.Surjective (kernelCosetToSaturationCoset d L K) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    have hzSup : (z : G) ∈ d.ker ⊔ L := by
      rw [sup_comm]
      exact z.property.2
    obtain ⟨n, hnKer, l, hlL, hnl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := d.ker) (t := L)).mp hzSup
    have hnK : n ∈ K := by
      rw [show n = (z : G) * l⁻¹ by rw [← hnl, mul_inv_cancel_right]]
      exact K.mul_mem z.property.1 (K.inv_mem (hLK hlL))
    let n' : ↑(K ⊓ d.ker) := ⟨n, hnK, hnKer⟩
    refine ⟨Quotient.mk'' n', ?_⟩
    simp only [kernelCosetToSaturationCoset, Quotient.map'_mk'']
    apply Quotient.eq''.mpr
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    change n⁻¹ * (z : G) ∈ L
    rw [← hnl]
    simpa using hlL
  exact Equiv.ofBijective (kernelCosetToSaturationCoset d L K)
    ⟨kernelCosetToSaturationCoset_injective d L K,
      kernelCosetToSaturationCoset_surjective d hLK⟩

end Langlands.NYLL.ClassFormation
