import Langlands.Representation.Classification.SegmentSocleProductCaseTwo
import Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement
import Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement
import Langlands.Representation.Derivative.MirabolicProductRestriction

/-!
# Zelevinsky 6.2 from its lower statements

Zelevinsky's Theorem 6.2 for every endpoint-separated segment-socle product,
assuming the exactness of the mirabolic minus functors, BZ77 4.13(c), 4.13(d),
BZ77 4.14(a), Ze80 5.3, Ze80 3.5, the highest derivative of a segment-socle
product, and the mirabolic support shift for cuspidal products (BZ77 4.7(b)).
BZ77 4.13(a) is the published theorem `mirabolicProductRestriction`.
`SegmentSocleProductHomogeneityInputs` is the conjunction of these lower
statements.
-/

noncomputable section

namespace Langlands.Classification

open Derivative SegmentSocleProductHomogeneityInduction SegmentSocleProductCaseTwo

universe uF uV

/-- The lower statements from which `segmentSocleProductHomogeneity_of` derives
Zelevinsky 1980, Theorem 6.2. -/
def SegmentSocleProductHomogeneityInputs {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : Prop :=
  Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T ∧
    MirabolicProductMinus.RightPhiShortExact.{uF, max uF uV} F T ∧
    MirabolicProductMinus.RightPhiBoundary.{uF, max uF uV} F T ∧
    RightMixedProductPhiMinusDetection.{uF, max uF uV} F T ∧
    LeftMixedProductDerivative.{uF, max uF uV} F T ∧
    LeftMixedProductHomogeneity.{uF, max uF uV} F T ∧
    SegmentSocleDerivatives.{uF, uV} F T ∧
    SegmentSocleProductHighestDerivative.{uF, uV} F T ∧
    CuspidalProductMirabolicSupportShift.{uF, uV} F T

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Zelevinsky 1980, Theorem 6.2, from the lower statements of its proof. -/
theorem segmentSocleProductHomogeneity_of
    (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
    (hS : MirabolicProductMinus.RightPhiShortExact.{uF, max uF uV} F T)
    (hB : MirabolicProductMinus.RightPhiBoundary.{uF, max uF uV} F T)
    (hD : RightMixedProductPhiMinusDetection.{uF, max uF uV} F T)
    (hLD : LeftMixedProductDerivative.{uF, max uF uV} F T)
    (hH : LeftMixedProductHomogeneity.{uF, max uF uV} F T)
    (h35 : SegmentSocleDerivatives.{uF, uV} F T)
    (hF : SegmentSocleProductHighestDerivative.{uF, uV} F T)
    (hC : CuspidalProductMirabolicSupportShift.{uF, uV} F T) :
    SegmentSocleProductHomogeneity.{uF, uV} F T := by
  intro ψ N d hd hsep
  have hl : d.length = (d.length - 1) + 1 := by
    rcases Nat.eq_zero_or_pos d.length with h0 | h0
    · have := d.degree_sum
      have he : IsEmpty (Fin d.length) := by rw [h0]; exact Fin.isEmpty'
      rw [Finset.univ_eq_empty, Finset.sum_empty] at this
      omega
    · omega
  exact homogeneous_of_caseTwo T ψ hE hD hS hB
    (mirabolicProductRestriction.{uF, max uF uV} F T) hLD (hH ψ) h35
    (fun d h m n ha hb hd hsep hP =>
      caseTwoExclusion T ψ hE hLD (hH ψ) (hC ψ) hF d h m n ha hb hd hsep hP)
    (d.length - 1) (N + 1) d N rfl hl hd hsep

/-- Zelevinsky 1980, Theorem 6.2, from the conjunction of its lower statements. -/
theorem segmentSocleProductHomogeneity_of_inputs
    (h : SegmentSocleProductHomogeneityInputs.{uF, uV} F T) :
    SegmentSocleProductHomogeneity.{uF, uV} F T := by
  obtain ⟨hE, hS, hB, hD, hLD, hH, h35, hF, hC⟩ := h
  exact segmentSocleProductHomogeneity_of T hE hS hB hD hLD hH h35 hF hC

end Langlands.Classification
