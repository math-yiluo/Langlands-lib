import Langlands.Representation.Aubert.MultisegmentRankOrder

/-! # Additivity and cancellation for the multisegment rank order -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.Multisegment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Rank order is preserved by adding two ordered pairs. -/
theorem RankLE.add {a a' b b' : Multisegment.{uV, uF} T}
    (ha : RankLE a' a) (hb : RankLE b' b) : RankLE (a' + b') (a + b) := by
  refine ⟨by simp only [cuspidalContent_add, ha.1, hb.1], fun I => ?_⟩
  simp only [containmentCount_add]
  exact Nat.add_le_add (ha.2 I) (hb.2 I)

/-- Adding the same multisegment reflects rank order. -/
theorem rankLE_add_right_iff (a b c : Multisegment.{uV, uF} T) :
    RankLE (a + c) (b + c) ↔ RankLE a b := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨?_, fun I => ?_⟩
    · simpa only [cuspidalContent_add, add_left_inj] using hc
    · simpa only [containmentCount_add, Nat.add_le_add_iff_right] using h I
  · intro h
    exact h.add (.refl c)

/-- If both factors are rank-lowered and their sum is unchanged, neither
factor changed. -/
theorem RankLE.eq_of_add_eq {a a' b b' : Multisegment.{uV, uF} T}
    (ha : RankLE a' a) (hb : RankLE b' b) (he : a' + b' = a + b) :
    a' = a ∧ b' = b := by
  have hrev : RankLE a a' := by
    refine ⟨ha.1.symm, fun I => ?_⟩
    have hs := congrArg (containmentCount I) he
    simp only [containmentCount_add] at hs
    have := hb.2 I
    omega
  have hea := ha.antisymm hrev
  exact ⟨hea, by simpa only [hea, add_right_inj] using he⟩

end Langlands.PadicField.TopologicalData.Multisegment
