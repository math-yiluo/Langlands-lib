import Langlands.Representation.Classification.SegmentSocleDerivativeConstituentSupport
import Langlands.Representation.Derivative.ProductDerivativeSupportAggregation
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof

/-! Actual support selectors for constituents of ordered-product derivatives. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentProductDerivativeConstituentSupport

open GeneralLinear PadicField.TopologicalData Derivative
open SegmentSocleDerivativeConstituentSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Every actual simple constituent of a segment-product derivative has the
support and derivative order selected by zero/rank choices at all positions. -/
theorem product_support
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (hd : d.HasSegmentSocles)
    (j : ℕ) (hj : j ≤ n)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - j) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n j hj).obj d.induced)) :
    ∃ bs : Fin d.length → Bool,
      j = (∑ i, if bs i then (d.segments i).rank else 0) ∧
      T.IsSupercuspidalSupport D
        (∑ i, residualContent T (d.segments i) (bs i)) := by
  let := T.topology
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : j = 0 := Nat.le_zero.mp hj
    let : IsEmpty (Fin d.length) := d.shape.isEmpty_blockIndex_rankZero
    refine ⟨fun _ => false, by simp, ?_⟩
    simpa using support_zero T D hD
  · let P : Fin d.length → ℕ → Multiset (CuspidalDatum.{uV, uF} T) → Prop :=
      fun i a s => ∃ b : Bool,
        a = (if b then (d.segments i).rank else 0) ∧
          s = residualContent T (d.segments i) b
    let f := ProductDerivativeSupport.supportData T ψ hn hj d.shape d.blocks D P
      (fun i a ha => generalLinearDerivativeFiniteLength F T ψ
        (d.segments i).degree a ha (d.blocks i)
        (hasFiniteLength_of_isIrreducible (hd i).choose_spec.2.1))
      (fun i a ha E hE hEA => by
        obtain ⟨b, hb, hs⟩ :=
          segment_support T ψ (d.segments i) (d.blocks i) (hd i) a ha E hE hEA
        exact ⟨_, ⟨b, hb, rfl⟩, hs⟩)
      hD hDP
    let bs : Fin d.length → Bool := fun i => Classical.choose (f.factors i).allowed
    have horder : ∀ i, (f.factors i).order =
        (if bs i then (d.segments i).rank else 0) :=
      fun i => (Classical.choose_spec (f.factors i).allowed).1
    have hcontent : ∀ i, (f.factors i).cuspidalSupport =
        residualContent T (d.segments i) (bs i) :=
      fun i => (Classical.choose_spec (f.factors i).allowed).2
    refine ⟨bs, ?_, ?_⟩
    · exact f.order_sum.symm.trans (Finset.sum_congr rfl (fun i _ => horder i))
    · have hs := f.support
      change T.IsSupercuspidalSupport D
        (∑ i : Fin d.length, (f.factors i).cuspidalSupport) at hs
      have heq : (∑ i : Fin d.length, (f.factors i).cuspidalSupport) =
          ∑ i : Fin d.length, residualContent T (d.segments i) (bs i) :=
        Finset.sum_congr rfl (fun i _ => hcontent i)
      rw [heq] at hs
      exact hs

/-- A support selector with its order equality and actual support witness. -/
def supportSelector
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n) (hd : d.HasSegmentSocles)
    (j : ℕ) (hj : j ≤ n)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - j) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n j hj).obj d.induced)) :
    {bs : Fin d.length → Bool //
      j = (∑ i, if bs i then (d.segments i).rank else 0) ∧
      T.IsSupercuspidalSupport D
        (∑ i, residualContent T (d.segments i) (bs i))} :=
  ⟨Classical.choose (product_support T ψ d hd j hj D hD hDP),
    Classical.choose_spec (product_support T ψ d hd j hj D hD hDP)⟩

end Langlands.Classification.SegmentProductDerivativeConstituentSupport
