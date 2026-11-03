import Langlands.Representation.Aubert.SupportGrading
import Langlands.Representation.Aubert.SegmentEndDerivation
import Langlands.Representation.Aubert.ZelevinskyPolynomial

/-!
# Injectivity of the segment polynomial evaluation from a derivation

If a ring endomorphism `D` of the graded Grothendieck ring acts on segment
classes as the total Bernstein–Zelevinsky derivative, the expansion
`E = μ ∘ D ∘ χ_1` of `SupportGrading` satisfies the hypothesis of
`SegmentEndDerivation.injective_of_endExpansion`, so the segment polynomial
evaluation is injective.
-/

noncomputable section

namespace Langlands.Aubert

open PadicField.TopologicalData SupportGrading

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- **Injectivity of the segment polynomial evaluation**, given any ring
endomorphism `D` of the graded Grothendieck ring acting on segment classes as
the total Bernstein–Zelevinsky derivative: `D ζ(Δ) = ζ(Δ) + 1` when `Δ` has
length one and `D ζ(Δ) = ζ(Δ) + ζ(Δ⁻)` otherwise. -/
theorem segmentPolynomialEvaluation_injective_of_derivation
    (D : letI := T.topology; letI := gradedInductionRing F T hx hl
      GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T)
    (hD₁ : letI := T.topology; letI := gradedInductionRing F T hx hl
      ∀ Δ : T.Segment.{max uF uV, uF}, Δ.length = 1 →
        D (gradedSegmentSocle F T Δ) = gradedSegmentSocle F T Δ + gradedUnit F T)
    (hD₂ : letI := T.topology; letI := gradedInductionRing F T hx hl
      ∀ (Δ : T.Segment.{max uF uV, uF}) (h : 2 ≤ Δ.length),
        D (gradedSegmentSocle F T Δ) =
          gradedSegmentSocle F T Δ + gradedSegmentSocle F T ⟨Δ.base, Δ.length - 1, by omega⟩) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    Function.Injective (segmentPolynomialEvaluation F T hx hl) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  refine SegmentEndDerivation.injective_of_endExpansion _ (expansion F T hx hl D) (fun Δ => ?_)
    (intCast_eq_zero F T hx hl)
  have hX : ∀ Δ' : T.Segment.{max uF uV, uF},
      segmentPolynomialEvaluation F T hx hl (MvPolynomial.X Δ') = gradedSegmentSocle F T Δ' :=
    fun Δ' => MvPolynomial.eval₂Hom_X' _ _ _
  rw [hX]
  by_cases h : 1 < Δ.length
  · rw [SegmentEndDerivation.endTail_of_one_lt h, hX]
    refine expansion_segmentSocle F T hx hl D Δ _
      (supportDegree T (Δ.dropLastNonempty h).cuspidalContent) (hD₂ Δ h) ?_ ?_
    · rw [supportTwist_segmentSocle, neg_smul, one_smul]
    · rw [cuspidalContent_dropLastNonempty Δ h, supportDegree_add, supportDegree_singleton]
  · have h1 : Δ.length = 1 := by have := Δ.length_pos; omega
    rw [SegmentEndDerivation.endTail_of_length_eq_one h1, map_one]
    refine expansion_segmentSocle F T hx hl D Δ _ 0 (hD₁ Δ h1) ?_ ?_
    · rw [neg_zero, map_one, AddMonoidAlgebra.one_def]
    · rw [cuspidalContent_of_length_eq_one Δ h1, supportDegree_singleton, zero_add]

end Langlands.Aubert
