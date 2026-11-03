import Langlands.Representation.Derivative.ProductDerivativeSupportAggregation
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationProof
import Langlands.Representation.Classification.SegmentHeadProductFiniteness

/-! Terminal support witnesses for actual derivatives of supplied head products. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData
open Derivative.ProductDerivativeSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The support set is an optional terminal truncation of the supplied segment.
No formula for the derivative or its order is part of this predicate. -/
def TerminalSupportPredicate (Δ : T.Segment.{uV, uF}) (_k : ℕ)
    (s : Multiset (T.CuspidalDatum.{uV, uF})) : Prop :=
  ∃ A : Option (T.Segment.{uV, uF}),
    Segment.IsTerminalTruncation A Δ ∧ {ρ | ρ ∈ s} = Segment.optionalSupport A

/-- Actual constituent data at every original segment label, with a terminal
support witness, for a derivative constituent of a supplied source subquotient. -/
def segmentHeadProductTerminalSupportDataOfSubquotient {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n)
    (d : T.SegmentProductDatum.{uV, uF} n) (hd : d.HasSegmentHeads)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology; SmoothRep.IsSubquotient Q d.induced)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n k hk).obj Q)) :
    SupportData T ψ d.shape d.blocks D
      (fun i => TerminalSupportPredicate T (d.segments i)) := by
  letI := T.topology
  apply supportDataOfSubquotient T ψ hn hk d.shape d.blocks Q hQ D
    (fun i => TerminalSupportPredicate T (d.segments i)) ?_ ?_ hD hDQ
  · intro i a ha
    exact generalLinearDerivativeFiniteLength.{uF, max uF uV} F T ψ
      (d.segments i).degree a ha (d.blocks i)
      (hasFiniteLength_of_isIrreducible (hd i).isIrreducible)
  · intro i a ha E hE hocc
    obtain ⟨s, A, hs, hA, heq⟩ :=
      segmentHeadDerivativeSupportTruncation.{uF, uV} F T ψ
        (d.segments i) (d.blocks i) (hd i) a ha E hE hocc
    exact ⟨s, ⟨A, hA, heq⟩, hs⟩

/-- The same original-label data for a constituent of the derivative of the
whole supplied head product. -/
def segmentHeadProductTerminalSupportData {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n)
    (d : T.SegmentProductDatum.{uV, uF} n) (hd : d.HasSegmentHeads)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n k hk).obj d.induced)) :
    SupportData T ψ d.shape d.blocks D
      (fun i => TerminalSupportPredicate T (d.segments i)) := by
  letI := T.topology
  exact segmentHeadProductTerminalSupportDataOfSubquotient T ψ hn hk d hd
    d.induced (SmoothRep.isSubquotient_iff_representation.mpr (WeylBranchPieces.IsSubquotient.refl _))
    D hD hDP

/-- Choose actual terminal truncations at the original labels and support
multisets whose sum supports the supplied derivative constituent. -/
theorem segmentHeadProductTerminalTruncationSupportOfSubquotient {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n)
    (d : T.SegmentProductDatum.{uV, uF} n) (hd : d.HasSegmentHeads)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology; SmoothRep.IsSubquotient Q d.induced)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n k hk).obj Q)) :
    ∃ (A : Fin d.length → Option (T.Segment.{uV, uF}))
      (s : Fin d.length → Multiset (T.CuspidalDatum.{uV, uF})),
      (∀ i, Segment.IsTerminalTruncation (A i) (d.segments i)) ∧
      (∀ i, {ρ | ρ ∈ s i} = Segment.optionalSupport (A i)) ∧
      T.IsSupercuspidalSupport D (∑ i, s i) := by
  let := T.topology
  let w := segmentHeadProductTerminalSupportDataOfSubquotient T ψ hn hk d hd Q hQ D hD hDQ
  let A := fun i => Classical.choose (w.factors i).allowed
  refine ⟨A, fun i => (w.factors i).cuspidalSupport, ?_, ?_, w.support⟩
  · intro i
    exact (Classical.choose_spec (w.factors i).allowed).1
  · intro i
    exact (Classical.choose_spec (w.factors i).allowed).2

/-- The underlying support set of the chosen sum is the union of the terminal
truncation supports. The supports themselves remain multisets. -/
theorem segmentHeadProductTerminalTruncationUnionOfSubquotient {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n)
    (d : T.SegmentProductDatum.{uV, uF} n) (hd : d.HasSegmentHeads)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology; SmoothRep.IsSubquotient Q d.induced)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n k hk).obj Q)) :
    ∃ (A : Fin d.length → Option (T.Segment.{uV, uF}))
      (s : Multiset (T.CuspidalDatum.{uV, uF})),
      (∀ i, Segment.IsTerminalTruncation (A i) (d.segments i)) ∧
      T.IsSupercuspidalSupport D s ∧
      {ρ | ρ ∈ s} = ⋃ i, Segment.optionalSupport (A i) := by
  obtain ⟨A, s, hA, hs, hsupport⟩ :=
    segmentHeadProductTerminalTruncationSupportOfSubquotient T ψ hn hk d hd Q hQ D hD hDQ
  refine ⟨A, ∑ i, s i, hA, hsupport, ?_⟩
  ext ρ
  simp only [Set.mem_ofPred_eq, Multiset.mem_sum, Finset.mem_univ, true_and,
    Set.mem_iUnion]
  exact exists_congr fun i => Set.ext_iff.mp (hs i) ρ

end Langlands.Classification
