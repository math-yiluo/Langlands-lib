import Langlands.Representation.Classification.SegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.BlockEquivalence

/-! # Real determinant twists of the four segment constituent relations -/

noncomputable section

namespace Langlands

open CategoryTheory GeneralLinear

universe uF uV

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Common real determinant twist of the actual increasing segment product. -/
def segmentInducedRealTwistEquiv {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (m : ℕ) (hr : 0 < r) (s : ℝ) :
    letI := T.topology
    (twist (T.determinantPowerCharacter (m * r) s)
      (T.segmentInduced A m hr).representation).Equiv
      (T.segmentInduced (T.segmentFactor A s) m hr).representation := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨realPowerCharacter T.normalizedAbsUnits s,
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s⟩
  have e :
      (twist (T.determinantPowerCharacter (m * r) s)
        (T.segmentInduced A m hr).representation).Equiv
        (T.normalizedProductInduced (BlockShape.uniform m r hr)
          (fun i => twist (T.determinantPowerCharacter r s)
            (T.segmentFactors A m hr i).representation)) :=
    T.normalizedProductDeterminantTwistEquiv (BlockShape.uniform m r hr) χ
      (fun i => (T.segmentFactors A m hr i).representation)
  have hblocks :
      (fun i : Fin (BlockShape.uniform m r hr).length =>
        twist (T.determinantPowerCharacter r s)
          (T.segmentFactors A m hr i).representation) =
      (fun i => (T.segmentFactors (T.segmentFactor A s) m hr i).representation) := by
    funext i
    change twist (T.determinantPowerCharacter r s)
        (twist (T.determinantPowerCharacter r (i : ℝ)) A.representation) =
      twist (T.determinantPowerCharacter r (i : ℝ))
        (twist (T.determinantPowerCharacter r s) A.representation)
    rw [twist_twist, twist_twist,
      mul_comm (T.determinantPowerCharacter r s) (T.determinantPowerCharacter r (i : ℝ))]
  have eblocks (i : Fin (BlockShape.uniform m r hr).length) :
      (twist (T.determinantPowerCharacter r s)
        (T.segmentFactors A m hr i).representation).Equiv
        (T.segmentFactors (T.segmentFactor A s) m hr i).representation :=
    equivOfRepresentationEq (congrFun hblocks i)
  exact e.trans
    (T.normalizedProductInducedEquiv (BlockShape.uniform m r hr) eblocks)

end PadicField.TopologicalData

namespace Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Real determinant twisting preserves and reflects all four segment relations. -/
theorem segmentConstituentRealTwistCompatibility :
    SegmentConstituentRealTwistCompatibility.{uF, uV} F T := by
  let := T.topology
  intro Δ s π
  obtain ⟨A, hA⟩ := Quotient.exists_rep Δ.base.cls
  let As := SupercuspidalRep.twist (T.determinantPowerCharacter Δ.rank s)
    (T.isOpen_ker_determinantPowerCharacter Δ.rank s)
    (T.ker_determinant_le_ker_determinantPowerCharacter Δ.rank s) A
  have hAs : (Δ.twist s).base.IsRepresentedBy As := by
    change SupercuspidalClass.twist _ _ _ A.isoClass =
      SupercuspidalClass.twist _ _ _ Δ.base.cls
    rw [show A.isoClass = Δ.base.cls from hA]
  have e := T.segmentInducedRealTwistEquiv A.obj Δ.length Δ.rank_pos s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [T.isSegmentSocle_iff Δ π A hA,
      T.isSegmentSocle_iff (Δ.twist s) _ As hAs]
    exact (isIrreducibleSocle_twist_iff _ _ _).symm.trans
      (isIrreducibleSocle_iff_of_equiv e)
  · rw [T.isSegmentHead_iff Δ π A hA,
      T.isSegmentHead_iff (Δ.twist s) _ As hAs]
    exact (isIrreducibleHead_twist_iff _ _ _).symm.trans
      (isIrreducibleHead_iff_of_equiv e)
  · rw [T.isSegmentSubrepresentation_iff Δ π A hA,
      T.isSegmentSubrepresentation_iff (Δ.twist s) _ As hAs]
    exact (isIrreducibleSubrepresentation_twist_iff _ _ _).symm.trans
      (isIrreducibleSubrepresentation_iff_of_equiv e)
  · rw [T.isSegmentQuotient_iff Δ π A hA,
      T.isSegmentQuotient_iff (Δ.twist s) _ As hAs]
    exact (isIrreducibleQuotient_twist_iff _ _ _).symm.trans
      (isIrreducibleQuotient_iff_of_equiv e)

end Classification

end Langlands
