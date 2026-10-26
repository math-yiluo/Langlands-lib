import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
import Mathlib.Logic.Relation

/-! # Positive integral shifts between segment bases

The acyclicity conclusions explicitly require integral twist freeness.
No proof of that representation-theoretic premise is supplied here.
-/

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- The second base is a positive integral twist of the first base.
There is no linkage requirement. -/
def PositiveBaseShift (Δ Γ : Segment.{uV, uF} T) : Prop :=
  ∃ k : ℕ, 0 < k ∧ Γ.base = Δ.base.twist (k : ℝ)

theorem Precedes.positiveBaseShift {Δ Γ : Segment.{uV, uF} T}
    (h : Δ.Precedes Γ) : Δ.PositiveBaseShift Γ := h.2

theorem PositiveBaseShift.trans {Δ Γ Λ : Segment.{uV, uF} T}
    (h : Δ.PositiveBaseShift Γ) (h' : Γ.PositiveBaseShift Λ) :
    Δ.PositiveBaseShift Λ := by
  obtain ⟨k, hk, hΓ⟩ := h
  obtain ⟨m, hm, hΛ⟩ := h'
  refine ⟨m + k, Nat.add_pos_left hm k, ?_⟩
  rw [hΛ, hΓ, CuspidalDatum.twist_twist, Nat.cast_add]

/-- Every nonempty finite precedence chain advances its base by a positive
integer, even though segment precedence need not be transitive. -/
theorem positiveBaseShift_of_transGen_precedes {Δ Γ : Segment.{uV, uF} T}
    (h : Relation.TransGen Segment.Precedes Δ Γ) : Δ.PositiveBaseShift Γ := by
  induction h with
  | single h => exact h.positiveBaseShift
  | tail _ h ih => exact ih.trans h.positiveBaseShift

/-- A positive base shift preserves the rank of the cuspidal bases. -/
theorem PositiveBaseShift.rank_eq {Δ Γ : Segment.{uV, uF} T}
    (h : Δ.PositiveBaseShift Γ) : Δ.rank = Γ.rank := by
  obtain ⟨k, _, hΓ⟩ := h
  exact (congrArg CuspidalDatum.rank hΓ).symm

/-- A positive base shift cannot return to its starting segment when actual
cuspidal integral twists are free. -/
theorem PositiveBaseShift.irrefl
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (Δ : Segment.{uV, uF} T) : ¬ Δ.PositiveBaseShift Δ := by
  rintro ⟨k, hk, heq⟩
  have hz : (k : ℤ) = 0 := (hfree Δ.base (k : ℤ)).mp (by simpa using heq.symm)
  have hk0 : k = 0 := by exact_mod_cast hz
  exact (Nat.ne_of_gt hk) hk0

/-- Integral twist freeness rules out every nonempty precedence cycle. -/
theorem not_transGen_precedes_self
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (Δ : Segment.{uV, uF} T) : ¬ Relation.TransGen Segment.Precedes Δ Δ :=
  fun h => PositiveBaseShift.irrefl hfree Δ (positiveBaseShift_of_transGen_precedes h)

/-- Under the same explicit freeness premise, a positive base shift excludes
the reverse positive base shift. -/
theorem PositiveBaseShift.not_reverse
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} (h : Δ.PositiveBaseShift Γ) :
    ¬ Γ.PositiveBaseShift Δ :=
  fun h' => PositiveBaseShift.irrefl hfree Δ (h.trans h')

theorem Precedes.not_reverse
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : Segment.{uV, uF} T} (h : Δ.Precedes Γ) : ¬ Γ.Precedes Δ :=
  fun h' => h.positiveBaseShift.not_reverse hfree h'.positiveBaseShift

end Segment

end Langlands.PadicField.TopologicalData
