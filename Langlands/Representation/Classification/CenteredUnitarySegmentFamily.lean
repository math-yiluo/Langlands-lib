import Langlands.Representation.Classification.CenteredUnitarySegmentParametrization
import Langlands.Representation.Classification.SegmentSpecialParameterUniquenessProof
import Langlands.Representation.Classification.HermitianParameterInvolution
import Langlands.Global.Factors.AppendixPoleCountingStatement

/-!
# Actual centered segment parameters for a Hermitian block family

The original segment-head description is retained so that the published
parameter-uniqueness theorem identifies matched segments. Their lengths then
supply the numerical symmetry needed for the Appendix pole argument.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem transported_head_iso
    {C : ℕ → Type*} [∀ n, Category (C n)]
    {a b n m : ℕ} (ha : a = n) (hb : b = m) (hr : n = m)
    (X : C n) (Y : C m) (he : Nonempty ((hr ▸ X) ≅ Y)) :
    Nonempty (((ha.trans (hr.trans hb.symm)) ▸ (ha.symm ▸ X)) ≅ (hb.symm ▸ Y)) := by
  cases ha
  cases hb
  exact he

/-- Actual isomorphic heads give equal original segments, including their
base classes, ranks and lengths, with every rank transport explicit. -/
theorem SquareIntegrableSegmentParameter.segment_eq_of_iso
    {n m : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (d : SquareIntegrableSegmentParameter F T n π)
    (d' : SquareIntegrableSegmentParameter F T m π')
    (hr : n = m)
    (he : letI := T.topology
      Nonempty ((hr ▸ π) ≅ π')) : d.segment = d'.segment := by
  let := T.topology
  exact segmentSpecialParameterUniqueness.{uF, uV} F T d.segment d'.segment
    (d.degree_eq.trans (hr.trans d'.degree_eq.symm))
    (d.degree_eq.symm ▸ π) (d'.degree_eq.symm ▸ π') d.head d'.head
    (transported_head_iso
      (C := fun n => SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      d.degree_eq d'.degree_eq hr π π' he)

/-- The same original parameters make the positive midpoint twist a strong
head of a segment with the chosen actual unitary base. -/
theorem SquareIntegrableSegmentParameter.centeredHead
    {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (d : SquareIntegrableSegmentParameter F T n π) :
    T.IsSegmentHead (d.segment.twist (((d.segment.length : ℝ) - 1) / 2))
      (T.segmentFactor (d.degree_eq.symm ▸ π) (((d.segment.length : ℝ) - 1) / 2)) := by
  let := T.topology
  exact (segmentConstituentRealTwistCompatibility.{uF, max uF uV} F T
    d.segment (((d.segment.length : ℝ) - 1) / 2)
    (d.degree_eq.symm ▸ π)).2.1.mp d.head

/-- Choose these parameters for every actual square-integrable block. -/
def IsUnitarySquareIntegrableBlockFamily.segmentParameters
    {n : ℕ} {B : BlockShape n}
    {δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (hδ : IsUnitarySquareIntegrableBlockFamily F T B δ) :
    ∀ i, SquareIntegrableSegmentParameter F T (B.size i) (δ i) :=
  fun i => squareIntegrableSegmentParameter F T (B.size i) (B.positive i) (δ i)
    (hδ i).1 (hδ i).2.2

/-- Hermitian matching identifies the full chosen segments and therefore
preserves the nonnegative length parameter used by the Appendix argument. -/
theorem IsUnitaryGenericDatum.exists_symmetricSegmentParameters
    {n : ℕ} {B : BlockShape n}
    {δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    {s : Fin B.length → ℝ}
    (h : IsUnitaryGenericDatum F T B δ s)
    (d : ∀ i, SquareIntegrableSegmentParameter F T (B.size i) (δ i)) :
    letI := T.topology
    ∃ (e : Fin B.length ≃ Fin B.length) (hr : ∀ i, B.size i = B.size (e i)),
      Global.PoleComparison.SymmetricBlockData
        (fun i => (d i).segment.length - 1) s e ∧
      ∀ i, (d i).segment = (d (e i)).segment ∧
        Nonempty ((hr i ▸ δ i) ≅ δ (e i)) := by
  let := T.topology
  obtain ⟨e, hr, hinv, he⟩ := h.2.2.exists_involutive
  have hd : ∀ i, (d i).segment = (d (e i)).segment := by
    intro i
    exact (d i).segment_eq_of_iso F T (d (e i)) (hr i) (he i).2
  refine ⟨e, hr, ⟨hinv, ?_, fun i => (he i).1, h.2.1⟩,
    fun i => ⟨hd i, (he i).2⟩⟩
  intro i
  exact congrArg (fun Δ : T.Segment.{max uF uV, uF} => Δ.length - 1) (hd i).symm

end Langlands.Classification
