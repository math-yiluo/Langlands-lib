/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs

/-!
# A representative commuting with a Frobenius lift stabilizes its fixed field

Modified by Worker 5264, 15 November 2026: prove the published target
`conjugate_frobeniusFixedField_eq_of_commutesStatement` (M042.002) by the
source proof of `conjugate_frobeniusFixedField_eq_of_commutes` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusClosureCommutation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
unfolded by an initial `show`, and rewrite with the published theorem
`conjugateClosedSubgroup_mem` (M026.002) through its unfolded statement. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

noncomputable section

section frobeniusClosureCommutation

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- If a quotient element commutes with the Frobenius lift, its chosen
representative stabilizes the corresponding fixed field. -/
theorem conjugate_frobeniusFixedField_eq_of_commutes (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    conjugate_frobeniusFixedField_eq_of_commutesStatement D K L hLK σ q hq := by
  show
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ
  dsimp only
  let T := D.frobeniusFixedField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ
  have hmem : x ∈ conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
      k.1⁻¹ * x * k.1⁻¹⁻¹ ∈ D.frobeniusFixedField K L hLK σ :=
    conjugateClosedSubgroup_mem (D.frobeniusFixedField K L hLK σ) k.1⁻¹ x
  rw [hmem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [this]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q * QuotientGroup.mk t * q⁻¹ = QuotientGroup.mk t := by
        calc
          q * QuotientGroup.mk t * q⁻¹ =
              (QuotientGroup.mk t * q) * q⁻¹ := by rw [hcomm']
          _ = QuotientGroup.mk t := mul_inv_cancel_right _ _
      change QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      have hxval : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hyClosure : QuotientGroup.mk yK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q⁻¹ * QuotientGroup.mk t * q = QuotientGroup.mk t := by
        calc
          q⁻¹ * QuotientGroup.mk t * q =
              q⁻¹ * (QuotientGroup.mk t * q) := by simp [mul_assoc]
          _ = q⁻¹ * (q * QuotientGroup.mk t) := by rw [hcomm']
          _ = QuotientGroup.mk t := inv_mul_cancel_left _ _
      have hyval : yK = k⁻¹ * t * k := by
        apply Subtype.ext
        dsimp [yK]
        have htxval : t.1 = x := by simpa using htx
        rw [htxval]
      rw [hyval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)⁻¹ *
          QuotientGroup.mk t * QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    refine ⟨yK, hyClosure, ?_⟩
    simp [yK]

end DegreeData

end frobeniusClosureCommutation

end

end Langlands.NYLL.ClassFormation
