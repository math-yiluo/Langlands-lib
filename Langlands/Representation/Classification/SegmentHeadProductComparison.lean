import Langlands.Representation.CuspidalSupport.FixedSupportDetectedEquiv
import Langlands.Representation.Classification.SegmentHeadProductCuspidalQuotient
import Langlands.Representation.Classification.SegmentHeadProductTopDerivative

/-! Actual comparison of special-head products with equal cuspidal contents. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- Every irreducible actual subquotient of a supplied head product has its
exact cuspidal-member multiset as a supercuspidal support. -/
theorem segmentHeadProductSubquotientCuspidalSupportIndependent {n : ℕ}
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (E : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hE : letI := T.topology; E.IsIrreducible)
    (hEd : letI := T.topology; SmoothRep.IsSubquotient E d.induced) :
    T.IsSupercuspidalSupport E d.multisegment.cuspidalContent := by
  let := T.topology
  let C := segmentHeadProductCuspidalQuotient T d hd
  refine ⟨C.length, C.members, C.content_eq, C.rank_sum,
    C.representatives, C.represents, hE, ?_⟩
  exact smoothSubquotientTransitivity ℂ _
    (T.cuspidalProductInduced C.members C.rank_sum C.representatives)
    d.induced E hEd
    (SmoothRep.IsQuotient.isSubquotient ⟨C.quotientMap, C.surjective⟩)

/-- A detected actual constituent of the second product and an actual
equivalence from the whole first product to that constituent. -/
structure SegmentHeadProductComparisonData
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (d e : T.SegmentProductDatum.{uV,uF} n) where
  detected : letI := T.topology
    ExactFunctorDetectedConstituent.Data
      (generalLinearDerivative T ψ n n le_rfl) e.induced
  equivalence : letI := T.topology
    d.induced.representation.Equiv detected.constituent.representation

/-- If the first head product is irreducible, equal cuspidal contents give an
actual equivalence with a detected constituent of the second head product. -/
def segmentHeadProductComparison
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (hn : 0 < n) (d e : T.SegmentProductDatum.{uV,uF} n)
    (hd : d.HasSegmentHeads) (he : e.HasSegmentHeads)
    (hirr : letI := T.topology; d.induced.IsIrreducible)
    (hcontent : d.multisegment.cuspidalContent = e.multisegment.cuspidalContent) :
    SegmentHeadProductComparisonData T ψ d e := by
  letI := T.topology
  let c := chooseSegmentHeadProductDetectedConstituent T ψ hn e he
  have hD := segmentHeadProductCuspidalSupportIndependent T d hd hirr
  have hE : T.IsSupercuspidalSupport c.constituent d.multisegment.cuspidalContent := by
    rw [hcontent]
    exact segmentHeadProductSubquotientCuspidalSupportIndependent T e he
      c.constituent c.irreducible c.occurs
  exact ⟨c, CuspidalSupport.fixedSupportDetectedEquiv T ψ hn
    d.induced c.constituent d.multisegment.cuspidalContent hD hE
    (segmentHeadProductTopDerivativeNontrivial T ψ hn d hd) c.image_nontrivial⟩

/-- The comparison exhibits the entire first product as an actual smooth
subquotient of the second product. -/
theorem SegmentHeadProductComparisonData.isSubquotient
    {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology}
    {n : ℕ} {d e : T.SegmentProductDatum.{uV,uF} n}
    (c : SegmentHeadProductComparisonData T ψ d e) :
    letI := T.topology
    SmoothRep.IsSubquotient d.induced e.induced := by
  let := T.topology
  exact SmoothRep.IsSubquotient.of_iso_left
    (SmoothRep.mkIso c.equivalence.symm) c.detected.occurs

/-- Every actual derivative preserves the subquotient supplied by the
comparison, including derivative order zero and the top order. -/
theorem SegmentHeadProductComparisonData.derivative_isSubquotient
    {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology}
    {n : ℕ} {d e : T.SegmentProductDatum.{uV,uF} n}
    (c : SegmentHeadProductComparisonData T ψ d e) (k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    SmoothRep.IsSubquotient
      ((generalLinearDerivative T ψ n k hk).obj d.induced)
      ((generalLinearDerivative T ψ n k hk).obj e.induced) := by
  let := T.topology
  exact ExactSmoothTransport.map_isSubquotient
    (generalLinearDerivative T ψ n k hk)
    (generalLinearDerivativeExactness F T ψ n k hk) (c.isSubquotient T)

end Langlands.Classification
