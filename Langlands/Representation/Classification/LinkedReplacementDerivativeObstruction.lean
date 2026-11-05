import Langlands.Representation.Classification.LinkedSegmentTerminalWitness
import Langlands.Representation.Classification.SegmentHeadProductTerminalSupport
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof

/-! Actual linked-pair terminal witnesses with a derivative obstruction for
their union/intersection replacement. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData}

private theorem replacementTerminalUnion {m : ℕ}
    (segments : Fin m → T.Segment.{uV, uF})
    (U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF}))
    (hsegments : List.ofFn segments = U :: I.toList)
    (A : Fin m → Option (T.Segment.{uV, uF}))
    (hA : ∀ i, Segment.IsTerminalTruncation (A i) (segments i)) :
    ∃ X Y : Option (T.Segment.{uV, uF}),
      Segment.IsTerminalTruncation X U ∧
      Segment.IsTerminalTruncationOfOptional Y I ∧
      (⋃ i, Segment.optionalSupport (A i)) =
        Segment.optionalSupport X ∪ Segment.optionalSupport Y := by
  cases I with
  | none =>
    have hm : m = 1 := by simpa using congrArg List.length hsegments
    subst m
    have h0 : segments 0 = U := by
      have h := congrArg (fun l => l[0]?) hsegments
      simpa using h
    refine ⟨A 0, none, ?_, rfl, ?_⟩
    · simpa only [h0] using hA 0
    · ext ρ
      simp [Segment.optionalSupport]
  | some J =>
    have hm : m = 2 := by simpa using congrArg List.length hsegments
    subst m
    have h0 : segments 0 = U := by
      have h := congrArg (fun l => l[0]?) hsegments
      simpa using h
    have h1 : segments 1 = J := by
      have h := congrArg (fun l => l[1]?) hsegments
      simpa using h
    refine ⟨A 0, A 1, ?_, ?_, ?_⟩
    · simpa only [h0] using hA 0
    · change Segment.IsTerminalTruncation (A 1) J
      simpa only [h1] using hA 1
    · ext ρ
      simp [Fin.exists_fin_two]

/-- A concrete terminal segment for the original linked pair, together with
nonoccurrence in every derivative of a supplied subquotient of its replacement
head product, for irreducible constituents with this support set. -/
structure LinkedReplacementDerivativeObstruction
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ Γ U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF})) where
  witness : Segment.LinkedTerminalWitness Δ Γ U I
  nonoccurrence : letI := T.topology
    ∀ (n k : ℕ) (hk : k < n)
      (d : T.SegmentProductDatum.{uV, uF} n),
      d.HasSegmentHeads → List.ofFn d.segments = U :: I.toList →
      ∀ (Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        SmoothRep.IsSubquotient Q d.induced →
      ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier)),
        D.IsIrreducible →
      ∀ s : Multiset (T.CuspidalDatum.{uV, uF}),
        T.IsSupercuspidalSupport D s →
        {ρ | ρ ∈ s} = witness.segment.support →
        ¬ SmoothRep.IsSubquotient D
          ((generalLinearDerivative T ψ n k (Nat.le_of_lt hk)).obj Q)

/-- Construct the actual witness and its replacement derivative obstruction
using only the published support-only terminal bound and support uniqueness. -/
def linkedReplacementDerivativeObstruction
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (hfree : CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U : T.Segment.{uV, uF}} {I : Option (T.Segment.{uV, uF})}
    (hp : Δ.Precedes Γ) (hs : Segment.IsUnionIntersectionReplacement Δ Γ U I) :
    LinkedReplacementDerivativeObstruction ψ Δ Γ U I := by
  letI := T.topology
  let w := Segment.linkedTerminalWitness hfree hp hs
  refine ⟨w, ?_⟩
  intro n k hk d hd hsegments Q hQ D hD s hsupp heq hocc
  obtain ⟨A, t, hA, ht, hset⟩ :=
    segmentHeadProductTerminalTruncationUnionOfSubquotient T ψ
      (by omega) (Nat.le_of_lt hk) d hd Q hQ D hD hocc
  have hst : s = t := Langlands.glSupercuspidalSupportUniqueness.{uV, uF}
    p F T (n - k) (by omega) D hD s t hsupp ht
  obtain ⟨X, Y, hX, hY, hXY⟩ :=
    replacementTerminalUnion d.segments U I hsegments A hA
  apply w.not_replacement X Y hX hY
  exact heq.symm.trans ((congrArg (fun z => {ρ | ρ ∈ z}) hst).trans
    (hset.trans hXY))

end Langlands.Classification
