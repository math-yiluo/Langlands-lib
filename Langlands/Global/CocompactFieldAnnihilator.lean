import Langlands.Global.CocompactPairingSeparation
import Mathlib.Data.Fintype.Pigeonhole

/-! # The annihilator of a cocompact infinite field -/

noncomputable section

open Set Filter Topology

universe u v

namespace Langlands.Global.CocompactFieldAnnihilator

open CocompactPairingSeparation

variable {K : Type u} [Field K]
variable {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The additive subgroup of parameters whose multiplication characters kill the field. -/
def fieldAnnihilator (ι : K →+* R) (ψ : AddChar R Circle) : AddSubgroup R where
  carrier := {a | ∀ k : K, ψ (a * ι k) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb k
    rw [add_mul, ψ.map_add_eq_mul, ha, hb, one_mul]
  neg_mem' := by
    intro a ha k
    rw [neg_mul, ψ.map_neg_eq_inv, ha, inv_one]

/-- Compact representatives and nondegeneracy force field self-annihilation. -/
theorem mem_iff_range [Infinite K] (ι : K →+* R)
    (ψ : AddChar R Circle) (hψ : Continuous ψ)
    (htriv : ∀ k : K, ψ (ι k) = 1)
    (C : Set R) (hC : IsCompact C)
    (hcover : ∀ y : R, ∃ k : K, y - ι k ∈ C)
    (hnondeg : ∀ a : R, (∀ y : R, ψ (a * y) = 1) → a = 0)
    (a : R) :
    a ∈ fieldAnnihilator ι ψ ↔ a ∈ Set.range ι := by
  classical
  constructor
  · intro ha
    have hpair : {p : R × R | p.1 - p.2 ∈ smallParameters ψ C} ∈
        𝓝 ((0 : R), (0 : R)) := by
      have hcont : ContinuousAt (fun p : R × R => p.1 - p.2) (0, 0) :=
        (continuous_fst.sub continuous_snd).continuousAt
      apply hcont
      simpa using smallParameters_mem_nhds ψ hψ C hC
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpair
    let W := U ∩ V
    have hW : W ∈ 𝓝 (0 : R) := inter_mem hU hV
    obtain ⟨t, _, ht⟩ := hC.elim_nhds_subcover
      (fun c => (fun d : R => d - c) ⁻¹' W)
      (fun c _ => by
        apply (continuous_id.sub continuous_const).continuousAt
        simpa using hW)
    choose k hk using fun s : K => hcover (ι s * a)
    let c (s : K) := ι s * a - ι (k s)
    have hc (s : K) : c s ∈ C := hk s
    have hcann (s : K) : c s ∈ fieldAnnihilator ι ψ := by
      intro l
      change ψ ((ι s * a - ι (k s)) * ι l) = 1
      rw [sub_mul, ψ.map_sub_eq_div,
        show (ι s * a) * ι l = a * ι (s * l) by rw [map_mul]; ring,
        ha, ← map_mul, htriv, div_self']
    have hcell (s : K) : ∃ j : t, c s - (j : R) ∈ W := by
      obtain ⟨j, hj, hs⟩ := mem_iUnion₂.mp (ht (hc s))
      exact ⟨⟨j, hj⟩, hs⟩
    choose cell hcell using hcell
    obtain ⟨s, r, hne, hsame⟩ := Finite.exists_ne_map_eq_of_infinite cell
    have hsmall : c s - c r ∈ smallParameters ψ C := by
      have hs := (hcell s).1
      have hr := (hcell r).2
      rw [← hsame] at hr
      have h := hUV (show (c s - (cell s : R), c r - (cell s : R)) ∈ U ×ˢ V
        from ⟨hs, hr⟩)
      change (c s - (cell s : R)) - (c r - (cell s : R)) ∈ smallParameters ψ C at h
      simpa only [sub_sub_sub_cancel_right] using h
    have hdiff : c s - c r ∈ fieldAnnihilator ι ψ :=
      (fieldAnnihilator ι ψ).sub_mem (hcann s) (hcann r)
    have heq : c s = c r := sub_eq_zero.mp
      (hnondeg _ (annihilates_of_small ι ψ C hcover _ hdiff hsmall))
    have hcoef : ι (s - r) * a = ι (k s - k r) := by
      dsimp [c] at heq
      rw [map_sub, map_sub]
      linear_combination heq
    refine ⟨(s - r)⁻¹ * (k s - k r), ?_⟩
    rw [map_mul, ← hcoef, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hne), map_one, one_mul]
  · rintro ⟨k, rfl⟩ l
    rw [← map_mul, htriv]

end Langlands.Global.CocompactFieldAnnihilator
