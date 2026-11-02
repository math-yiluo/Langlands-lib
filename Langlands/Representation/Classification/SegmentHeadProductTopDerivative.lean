import Langlands.Representation.Classification.SegmentHeadTopDerivative
import Langlands.Representation.Derivative.FiniteTopLine
import Langlands.Representation.Filtration.ExactFunctorDetectedConstituent
import Langlands.Representation.Filtration.ExactFunctorIrreducibility

/-! Top derivative and detected constituent data for a supplied head product. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Classification

open Langlands.GeneralLinear Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The whole top derivative of an arbitrary supplied product of special heads
is a complex line, without a linkage or ordering hypothesis. -/
def segmentHeadProductTopDerivativeLineEquiv {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads) :
    letI := T.topology
    ((generalLinearDerivative T ψ n n le_rfl).obj d.induced) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  exact finiteProductTopDerivativeLineEquiv T ψ hn d.shape d.blocks
    (fun i => segmentHeadTopDerivativeLineEquiv T ψ (d.segments i) (d.blocks i) (hd i))

/-- Every supplied positive-rank product has nonzero entire top derivative. -/
theorem segmentHeadProductTopDerivativeNontrivial {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads) :
    letI := T.topology
    Nontrivial ((generalLinearDerivative T ψ n n le_rfl).obj d.induced) := by
  let := T.topology
  exact (segmentHeadProductTopDerivativeLineEquiv T ψ hn d hd).toEquiv.nontrivial

/-- Choose an actual irreducible subquotient with nonzero top derivative and
actual equivalences to all such subquotients of this same head product. -/
def chooseSegmentHeadProductDetectedConstituent {n : ℕ} (hn : 0 < n)
    (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads) :
    letI := T.topology
    ExactFunctorDetectedConstituent.Data
      (generalLinearDerivative T ψ n n le_rfl) d.induced := by
  letI := T.topology
  let J := generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl
  have hJ : Mirabolic.MapsShortExactIntertwiners J :=
    generalLinearDerivativeExactness F T ψ n n le_rfl
  letI := ExactFunctorIrreducibility.preservesZero_of_exact J hJ
  let e := segmentHeadProductTopDerivativeLineEquiv T ψ hn d hd
  have hirr : (J.obj d.induced).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one (J.obj d.induced)
      (e.finrank_eq.trans (Module.finrank_self ℂ))
  exact ExactFunctorDetectedConstituent.choose J hJ d.induced
    (hd.hasFiniteLength hn) hirr

/-- Nonvanishing on every irreducible actual subquotient is the additional
condition sufficient for irreducibility of the supplied head product. -/
theorem segmentHeadProductIsIrreducible_of_topDerivativeNonvanishing {n : ℕ}
    (hn : 0 < n) (d : T.SegmentProductDatum.{uV,uF} n) (hd : d.HasSegmentHeads)
    (hdet : letI := T.topology
      ExactFunctorIrreducibility.NonvanishingOnIrreducibleSubquotients
        (generalLinearDerivative T ψ n n le_rfl) d.induced) :
    letI := T.topology
    d.induced.IsIrreducible := by
  let := T.topology
  let J := generalLinearDerivative.{uF,max uF uV} T ψ n n le_rfl
  let e := segmentHeadProductTopDerivativeLineEquiv T ψ hn d hd
  exact ExactFunctorIrreducibility.isIrreducible_of_finrank_obj_eq_one J
    (generalLinearDerivativeExactness F T ψ n n le_rfl) d.induced
    (hd.hasFiniteLength hn) hdet (e.finrank_eq.trans (Module.finrank_self ℂ))

end Langlands.Classification
