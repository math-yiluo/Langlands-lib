import Langlands.Group.TitsBorelChambers
import Mathlib.Data.Set.Card

/-! # Three Borel conjugates in a strict overgroup -/

noncomputable section

namespace Langlands.Group

open TitsSystem RelativeWeyl

universe u v

variable {G : Type u} {W : Type v} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace TitsSystem

/-- Conjugates of `B` contained in a given subgroup. -/
def borelsBelow (B Q : Subgroup G) : Set (Subgroup G) :=
  {H | (∃ g : G, H = conjugateSubgroup g B) ∧ H ≤ Q}

end TitsSystem

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

theorem conjugate_borel_eq_self_iff (g : G) :
    conjugateSubgroup g B = B ↔ g ∈ B := by
  constructor
  · intro hg
    exact (h.conjugate_borel_le_iff le_rfl g).mp hg.le
  · exact conjugateSubgroup_eq_self

theorem conjugate_borel_eq_iff (g k : G) :
    conjugateSubgroup g B = conjugateSubgroup k B ↔ k⁻¹ * g ∈ B := by
  constructor
  · intro heq
    apply (h.conjugate_borel_eq_self_iff _).mp
    have H := congrArg (conjugateSubgroup k⁻¹) heq
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
  · intro hmem
    calc
      conjugateSubgroup g B =
          conjugateSubgroup k (conjugateSubgroup (k⁻¹ * g) B) := by
        rw [← conjugateSubgroup_mul]
        simp
      _ = conjugateSubgroup k B := by rw [conjugateSubgroup_eq_self hmem]

/-- Any strict overgroup of `B` contains a representative of a simple reflection. -/
theorem exists_simple_rep_mem_of_lt {Q : Subgroup G} (hBQ : B < Q) :
    ∃ s ∈ S, ∃ n : N, π n = s ∧ (n : G) ∈ Q := by
  obtain ⟨X, hXS, hQ⟩ := h.exists_eq_standardParabolic Q hBQ.le
  have hX : X.Nonempty := by
    by_contra hX
    have hX0 : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hX
    have hQB : Q = B := SetLike.coe_injective (by
      rw [hQ, hX0, h.standardParabolic_empty])
    exact (ne_of_lt hBQ) hQB.symm
  obtain ⟨s, hs⟩ := hX
  obtain ⟨n, hn⟩ := h.surjective s
  exact ⟨s, hXS hs, n, hn,
    rep_mem_of_coe_eq hQ (hn ▸ Subgroup.subset_closure hs)⟩

/-- TS 4 supplies a third Borel conjugate alongside `B` and its simple translate. -/
theorem exists_three_borelsBelow_of_lt {Q : Subgroup G} (hBQ : B < Q) :
    ∃ H₀ ∈ borelsBelow B Q, ∃ H₁ ∈ borelsBelow B Q, ∃ H₂ ∈ borelsBelow B Q,
      H₀ ≠ H₁ ∧ H₀ ≠ H₂ ∧ H₁ ≠ H₂ := by
  obtain ⟨s, hs, n, hn, hnQ⟩ := h.exists_simple_rep_mem_of_lt hBQ
  have hnB : (n : G) ∉ B := by
    intro hnB
    exact h.ne_one s hs (hn.symm.trans ((h.mem_iff n).mp hnB))
  have hninv : π n⁻¹ = s := by rw [map_inv, hn, h.inv_eq hs]
  obtain ⟨b, hb, hbn⟩ := h.conj_not_le s hs n⁻¹ hninv
  have hbnB : b * (n : G) ∉ B := by
    intro hbnB
    exact hnB (by simpa [mul_assoc] using B.mul_mem (B.inv_mem hb) hbnB)
  refine ⟨B, ⟨⟨1, (conjugateSubgroup_one B).symm⟩, hBQ.le⟩,
    conjugateSubgroup (n : G) B,
    ⟨⟨n, rfl⟩, (h.conjugate_borel_le_iff hBQ.le _).mpr hnQ⟩,
    conjugateSubgroup (b * (n : G)) B,
    ⟨⟨b * (n : G), rfl⟩,
      (h.conjugate_borel_le_iff hBQ.le _).mpr (Q.mul_mem (hBQ.le hb) hnQ)⟩,
    ?_, ?_, ?_⟩
  · intro heq
    exact hnB ((h.conjugate_borel_eq_self_iff _).mp heq.symm)
  · intro heq
    exact hbnB ((h.conjugate_borel_eq_self_iff _).mp heq.symm)
  · intro heq
    have H := (h.conjugate_borel_eq_iff (b * (n : G)) (n : G)).mp heq.symm
    exact hbn (by simpa [mul_assoc] using H)

/-- Conjugating the strict inclusion gives the same three-Borel conclusion. -/
theorem exists_three_borelsBelow_of_conjugate_lt {Q : Subgroup G} (g : G)
    (hBQ : conjugateSubgroup g B < Q) :
    ∃ H₀ ∈ borelsBelow B Q, ∃ H₁ ∈ borelsBelow B Q, ∃ H₂ ∈ borelsBelow B Q,
      H₀ ≠ H₁ ∧ H₀ ≠ H₂ ∧ H₁ ≠ H₂ := by
  let Q' := conjugateSubgroup g⁻¹ Q
  have hBQ' : B < Q' := by
    constructor
    · have H := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hBQ.le
      change conjugateSubgroup g⁻¹ (conjugateSubgroup g B) ≤ Q' at H
      simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
    · intro hle
      have H := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
      change conjugateSubgroup g Q' ≤ conjugateSubgroup g B at H
      have H' : Q ≤ conjugateSubgroup g B := by
        simpa only [Q', ← conjugateSubgroup_mul, mul_inv_cancel,
          conjugateSubgroup_one] using H
      exact not_le_of_gt hBQ H'
  obtain ⟨H₀, h₀, H₁, h₁, H₂, h₂, h₀₁, h₀₂, h₁₂⟩ :=
    h.exists_three_borelsBelow_of_lt hBQ'
  have hmem : ∀ H ∈ borelsBelow B Q', conjugateSubgroup g H ∈ borelsBelow B Q := by
    rintro H ⟨⟨k, rfl⟩, hle⟩
    refine ⟨⟨g * k, (conjugateSubgroup_mul g k B).symm⟩, ?_⟩
    have H := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
    change conjugateSubgroup g (conjugateSubgroup k B) ≤ conjugateSubgroup g Q' at H
    simpa only [Q', ← conjugateSubgroup_mul, mul_inv_cancel,
      conjugateSubgroup_one] using H
  have hinj : Function.Injective (conjugateSubgroup g : Subgroup G → Subgroup G) := by
    intro H K hHK
    have H := congrArg (conjugateSubgroup g⁻¹) hHK
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one] using H
  exact ⟨_, hmem _ h₀, _, hmem _ h₁, _, hmem _ h₂,
    fun heq => h₀₁ (hinj heq), fun heq => h₀₂ (hinj heq), fun heq => h₁₂ (hinj heq)⟩

theorem three_le_encard_borelsBelow_of_conjugate_lt {Q : Subgroup G} (g : G)
    (hBQ : conjugateSubgroup g B < Q) :
    3 ≤ (borelsBelow B Q).encard := by
  obtain ⟨H₀, h₀, H₁, h₁, H₂, h₂, h₀₁, h₀₂, h₁₂⟩ :=
    h.exists_three_borelsBelow_of_conjugate_lt g hBQ
  have hsub : {H₀, H₁, H₂} ⊆ borelsBelow B Q := by
    intro H hH
    rcases hH with rfl | rfl | rfl
    · exact h₀
    · exact h₁
    · exact h₂
  have hcard : ({H₀, H₁, H₂} : Set (Subgroup G)).encard = 3 :=
    Set.encard_eq_three.mpr ⟨H₀, H₁, H₂, h₀₁, h₀₂, h₁₂, rfl⟩
  rw [← hcard]
  exact Set.encard_le_encard hsub

end IsTitsSystem
end Langlands.Group
