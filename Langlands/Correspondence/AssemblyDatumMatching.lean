import Langlands.Correspondence.AssemblyLReduction
import Langlands.Correspondence.AssemblyEpsilonRemainingReduction
import Langlands.Representation.Classification.LanglandsDatumRealization

/-!
# Recovering datum matching from datum existence and classification

The existence of one presenting datum whose blocks are segment heads suffices
for matching every presenting datum, provided the square-integrable Langlands
classification is supplied. Both premises remain explicit.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open CategoryTheory PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyDatumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyDatumGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- A segment-head model transports along a rank equality and an actual
equivalence to another model. -/
theorem IsSegmentHeadModel.of_rankEquiv
    {Δ : Segment.{uA, uF} F.canonicalTopologicalData} {n n' : ℕ}
    {Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier)}
    {Q' : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n' F.Carrier)}
    (h : n = n') (e : (h ▸ Q).representation.Equiv Q'.representation)
    (hQ' : IsSegmentHeadModel F Δ Q') : IsSegmentHeadModel F Δ Q := by
  cases h
  obtain ⟨hn, P, hP, ⟨e'⟩⟩ := hQ'
  subst hn
  exact ⟨rfl, P, hP, ⟨e.trans e'⟩⟩

private def blockEquivOfUniverseLiftIso {n n' : ℕ}
    (Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier))
    (Q' : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n' F.Carrier))
    (h : n = n')
    (e : (h ▸ SmoothRep.universeLift.{uF} Q) ≅ SmoothRep.universeLift.{uF} Q') :
    (h ▸ Q).representation.Equiv Q'.representation := by
  cases h
  exact (SmoothRep.universeLiftEquiv Q).trans
    ((SmoothRep.equivOfIso e).trans (SmoothRep.universeLiftEquiv Q').symm)

/-- The conditional passage from one matching presenting datum to matching
every presenting datum, with square-integrable classification supplied. -/
def AssemblyDatumMatchingReductionStatement : Prop :=
  MultisegmentHeadDatumExistence.{uF, uA} F →
    Classification.SquareIntegrableLanglandsClassification.{uF, uA}
      F F.canonicalTopologicalData →
        MultisegmentHeadDatumMatching.{uF, uA} F

/-- One matching presenting datum and the supplied square-integrable
classification give matching for every presenting datum. The classification
is applied after lifting the block carriers; rank zero is handled directly. -/
theorem multisegmentHeadDatumMatching_of_existence_and_classification
    (hE : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hC : Classification.SquareIntegrableLanglandsClassification.{uF, uA}
      F F.canonicalTopologicalData) :
    MultisegmentHeadDatumMatching.{uF, uA} F := by
  intro r Δ n J hJ
  obtain ⟨d0, hd0, φ0, hφ0⟩ := hE r Δ J hJ
  refine ⟨⟨d0, hd0⟩, fun d hd => ?_⟩
  by_cases hn : n = 0
  · subst n
    have hlen : d.shape.length = 0 := Nat.eq_zero_of_le_zero d.shape.length_le
    have hlen0 : d0.shape.length = 0 := Nat.eq_zero_of_le_zero d0.shape.length_le
    refine ⟨(finCongr (hlen.trans hlen0.symm)).trans φ0, fun k => ?_⟩
    have hk := k.isLt
    omega
  · let dl := d.universeLift.{uF, uA, uF}
    let d0l := d0.universeLift.{uF, uA, uF}
    have hdl : dl.IsLanglandsQuotient J :=
      Classification.IsIrreducibleQuotient.of_equiv
        d.universeLiftInducedEquiv hd
    have hd0l : d0l.IsLanglandsQuotient J :=
      Classification.IsIrreducibleQuotient.of_equiv
        d0.universeLiftInducedEquiv hd0
    obtain ⟨φ, hφ⟩ :=
      (hC n (Nat.pos_of_ne_zero hn) dl d0l J J hdl hd0l).mp ⟨Iso.refl J⟩
    refine ⟨φ.trans φ0, fun k => ?_⟩
    obtain ⟨hk, ⟨ek⟩⟩ := hφ k
    exact IsSegmentHeadModel.of_rankEquiv F hk
      (blockEquivOfUniverseLiftIso F (d.blocks k) (d0.blocks (φ k)) hk ek)
      (hφ0 (φ k))

/-- An assembly inherits epsilon compatibility from datum existence, the
supplied square-integrable classification, and segment-pair inheritance. -/
theorem assemblyEpsilonInheritance_of_datumExistence_classification_and_segmentPairs
    (hE : MultisegmentHeadDatumExistence.{uF, uA} F)
    (hC : Classification.SquareIntegrableLanglandsClassification.{uF, uA}
      F F.canonicalTopologicalData)
    (hS : SupercuspidalSegmentPairInheritance.{uF, uP, uA} F) :
    AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_datumMatching_and_segmentPairs F
    (multisegmentHeadDatumMatching_of_existence_and_classification F hE hC) hS

end Langlands.Correspondence
