import Langlands.Representation.Classification.SegmentGenericStatement
import Langlands.Representation.Classification.SegmentHeadProductIrreducibilityProof
import Langlands.Representation.Classification.SegmentHeadProductCuspidalSupportProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.UnlinkedCuspidalContentInjectivityProof
import Langlands.Representation.Classification.SegmentHeadProductTopDerivative
import Langlands.Representation.CuspidalSupport.FixedSupportDetectedEquiv
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! # Unordered uniqueness for unlinked products of special segment heads -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory PadicField.TopologicalData

universe uF uV

/-- Two unlinked products of supplied special heads are isomorphic exactly
when their segment multisets agree, including repeated occurrences. -/
theorem genericSegmentProductUniqueness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    GenericSegmentProductUniqueness.{uF, uV} F T := by
  let := T.topology
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  intro n d e hd he hu hv
  have hdI : d.induced.IsIrreducible :=
    (segmentHeadProductIrreducibility.{uF, max uF uV} F T n d hd).mpr hu
  have heI : e.induced.IsIrreducible :=
    (segmentHeadProductIrreducibility.{uF, max uF uV} F T n e he).mpr hv
  have hdS := segmentHeadProductCuspidalSupport.{uF, uV} F T (n + 1) d hd hdI
  have heS := segmentHeadProductCuspidalSupport.{uF, uV} F T (n + 1) e he heI
  constructor
  · rintro ⟨i⟩
    have hcontent : d.multisegment.cuspidalContent = e.multisegment.cuspidalContent :=
      Langlands.glSupercuspidalSupportUniqueness.{max uF uV, uF}
        p F T (n + 1) (Nat.succ_pos n) d.induced hdI _ _ hdS
        (heS.of_iso i.symm)
    exact unlinkedCuspidalContentInjectivity.{uF, max uF uV} F T _ _ hu hv hcontent
  · intro hm
    have heS' : T.IsSupercuspidalSupport e.induced d.multisegment.cuspidalContent := by
      rw [hm]
      exact heS
    exact ⟨SmoothRep.mkIso
      (CuspidalSupport.fixedSupportDetectedEquiv.{uF, max uF uV}
        T ψ (Nat.succ_pos n) d.induced e.induced d.multisegment.cuspidalContent hdS heS'
        (segmentHeadProductTopDerivativeNontrivial.{uF, max uF uV}
          T ψ (Nat.succ_pos n) d hd)
        (segmentHeadProductTopDerivativeNontrivial.{uF, max uF uV}
          T ψ (Nat.succ_pos n) e he))⟩

end Langlands.Classification
