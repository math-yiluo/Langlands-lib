import Langlands.Representation.Classification.SegmentHeadContragredient
import Langlands.Representation.Classification.SegmentIntervalLinkage
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-! Integral coordinates and precedence for endpoint-reversed dual segments. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open Classification Classification.CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- Duality reflects an integral segment interval through zero. -/
theorem HasIntegralCoordinates.dual
    {Δ : Segment.{uV, uF} T} {ρ : CuspidalDatum.{uV, uF} T} {a b : ℤ}
    (h : Δ.HasIntegralCoordinates ρ a b) :
    Δ.dual.HasIntegralCoordinates (dualDatum ρ) (-b) (-a) := by
  refine ⟨?_, ?_⟩
  · change dualDatum (Δ.base.twist ((Δ.length - 1 : ℕ) : ℝ)) = _
    rw [h.1, CuspidalDatum.twist_twist, dualDatum_twist]
    congr 1
    have hb : ((Δ.length - 1 : ℕ) : ℤ) + a = b := by
      have := h.2
      have := Δ.length_pos
      omega
    have hb' := congrArg (fun k : ℤ => (k : ℝ)) hb
    push_cast at hb' ⊢
    linarith
  · have := h.2
    simp only [dual_length]
    omega

/-- Endpoint-reversed duality reverses segment precedence. -/
theorem Precedes.dual {Δ Γ : Segment.{uV, uF} T} (h : Δ.Precedes Γ) :
    Γ.dual.Precedes Δ.dual := by
  have hfree := cuspidalIntegralTwistFreeness F T
  have hΔ := Δ.hasIntegralCoordinates_self
  obtain ⟨c, d, hΓ⟩ := hΔ.of_precedes_right h
  have hi := hΔ.intervalPrecedes_of_precedes hfree hΓ h
  apply hΓ.dual.precedes_of_intervalPrecedes hfree hΔ.dual
  unfold IntervalPrecedes at hi ⊢
  omega

/-- The duality involution makes precedence reversal an equivalence. -/
theorem precedes_dual_iff (Δ Γ : Segment.{uV, uF} T) :
    Δ.dual.Precedes Γ.dual ↔ Γ.Precedes Δ := by
  constructor
  · intro h
    simpa only [dual_dual] using h.dual
  · exact Precedes.dual

end Segment

end Langlands.PadicField.TopologicalData
