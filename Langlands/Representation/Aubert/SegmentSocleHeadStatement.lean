import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Classification.Segments

/-!
# Aubert duality from the segment socle to its special head

This proposition records the segment case of Aubert's Theorem 2.3, retaining
the support-dependent sign of Remark 2.2 for the unadjusted alternating
operator. It uses actual strong constituent relations and exact
finite-length classes. No segment-duality proof is supplied here.
-/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual segment socle and special head are exchanged by the existing
unadjusted Aubert operator with sign `(-1)^(degree - length)`.
Both finite-length witnesses follow from the irreducibility clauses of the
strong constituent relations. This asserts no constituent existence. -/
def SegmentSocleHeadStatement : Prop :=
  letI := T.topology
  ∀ (Δ : T.Segment.{max uF uV, uF})
    (πZ πS : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hZ : T.IsSegmentSocle Δ πZ) (hS : T.IsSegmentHead Δ πS),
    let x := GeneralLinear.finiteLengthClass Δ.degree F.Carrier πZ
      (SmoothRep.hasFiniteLength_of_isIrreducible (by
        obtain ⟨_, _, h⟩ := hZ
        exact h.1))
    let y := GeneralLinear.finiteLengthClass Δ.degree F.Carrier πS
      (SmoothRep.hasFiniteLength_of_isIrreducible (by
        obtain ⟨_, _, h⟩ := hS
        exact h.1))
    alternatingOperator.{uF, uV} F T Δ.degree x =
      (-1 : ℤ) ^ (Δ.degree - Δ.length) • y

end Langlands.Aubert
