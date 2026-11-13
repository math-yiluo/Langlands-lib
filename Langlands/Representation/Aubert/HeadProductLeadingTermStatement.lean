import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Aubert.MultisegmentRankOrder
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Smooth.IrreducibleCompositionFactors

/-! # Rank bounds and leading multiplicity for products of actual Langlands heads -/

noncomputable section

namespace Langlands.Aubert

open PadicField.TopologicalData SmoothRep
open SmoothRep.IrreducibleGrothendieckProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- In every natural rank, actual head-labelled constituents of a binary
normalized product satisfy the multisegment rank bound; the sum label has
composition multiplicity one; and any different constituent label below a
uniform-length sum contains a longer segment. -/
def HeadProductLeadingTermStatement : Prop :=
  letI := T.topology
  ∀ (m n : ℕ)
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n)
    (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n))
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
    dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B → dC.IsLanglandsQuotient C →
    (IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
      Multisegment.RankLE dC.multisegment (dA.multisegment + dB.multisegment)) ∧
    (dC.multisegment = dA.multisegment + dB.multisegment →
      ∀ hfin :
          ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).HasFiniteLength,
        compositionMultiplicity
          ⟨(T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B), hfin⟩ C = 1) ∧
    (∀ l : ℕ,
      IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
      (∀ Δ ∈ dA.multisegment + dB.multisegment, Δ.length = l) →
      dC.multisegment ≠ dA.multisegment + dB.multisegment →
      ∃ Δ ∈ dC.multisegment, l < Δ.length)

end Langlands.Aubert
