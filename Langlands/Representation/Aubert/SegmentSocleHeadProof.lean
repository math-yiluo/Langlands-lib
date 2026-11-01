import Langlands.Representation.Aubert.SegmentInductionAubertImage
import Langlands.Representation.Aubert.SegmentSocleHeadReduction

/-! Actual segment socle-to-special-head Aubert exchange. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic Classification SegmentFullJacquet
open SmoothRep.IrreducibleOperator

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The existing unadjusted Aubert operator exchanges the supplied actual
strong segment socle and special head with the support-dependent sign. -/
theorem segmentSocleHead : SegmentSocleHeadStatement.{uF, uV} F T := by
  let := T.topology
  intro Δ πZ πS hZ hS
  obtain ⟨A, _hA, hZi, j, hj⟩ := hZ.isSegmentSubrepresentation
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos)
  let I := T.segmentInduced A.obj Δ.length Δ.rank_pos
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T
    Δ.length Δ.length_pos Δ.rank_pos A
  let hI := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B σ
    (SmoothRep.hasFiniteLength_of_isIrreducible hσ.1)
  have hsub : SmoothRep.IsSubquotient πZ I :=
    (mem_support_compositionFactors_iff_isSubquotient ⟨I, hI⟩ πZ hZi).mp
      (mem_support_compositionFactors_of_injective πZ I hZi hI j hj)
  obtain ⟨τ, hτ, hImage⟩ := segmentInductionAubertImage.{uF, uV} F T
    Δ.length Δ.rank Δ.length_pos Δ.rank_pos A πZ hZi hsub
  rcases hImage with hImage | hImage
  · exact segmentSocleHead_of_signedIrreducibleImage F T
      Δ πZ πS τ hZ hS hτ 1 (Or.inl rfl) (by
        simpa only [one_smul] using hImage)
  · exact segmentSocleHead_of_signedIrreducibleImage F T
      Δ πZ πS τ hZ hS hτ (-1) (Or.inr rfl) (by
        simpa only [neg_one_smul] using hImage)

end Langlands.Aubert
