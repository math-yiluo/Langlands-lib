import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! Actual finite composition series for products of supplied segment heads. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Irreducibility is already part of the supplied strong head relation. -/
theorem IsSegmentHead.isIrreducible
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) :
    letI := T.topology
    π.IsIrreducible := by
  obtain ⟨_, _, h⟩ := hπ
  exact h.1

/-- Supplied segment heads are admissible for the supplied topology. -/
theorem IsSegmentHead.isAdmissible
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) :
    letI := T.topology
    π.IsAdmissible := by
  let := T.topology
  exact (CuspidalSupport.cuspidalEmbedding F T Δ.degree π hπ.isIrreducible).1

namespace SegmentProductDatum

variable {n : ℕ} {d : SegmentProductDatum.{uV,uF} T n}

/-- Admissibility holds for a product of supplied heads in any total rank. -/
theorem HasSegmentHeads.isAdmissible (hd : d.HasSegmentHeads) :
    letI := T.topology
    d.induced.IsAdmissible := by
  let := T.topology
  apply Parabolic.normalizedInductionAdmissibility F T d.shape
  exact FiniteTensor.isAdmissible_external _
    (fun i => (hd i).isAdmissible)

/-- Positive-rank products of supplied heads have finite group-algebra length. -/
theorem HasSegmentHeads.hasFiniteLength (hd : d.HasSegmentHeads) (hn : 0 < n) :
    letI := T.topology
    d.induced.HasFiniteLength := by
  let := T.topology
  exact irreducibleProductFiniteLength F T n hn d.shape d.blocks
    (fun i => (hd i).isIrreducible)

/-- Choose an actual finite composition series of the supplied head product. -/
def compositionSeriesOfHeads (d : SegmentProductDatum.{uV,uF} T n)
    (hd : d.HasSegmentHeads) (hn : 0 < n) :
    letI := T.topology
    Σ m : ℕ, {s : ObjectRepFiltration d.induced.obj m // s.HasSimpleFactors} := by
  let := T.topology
  exact Classical.choice (by
    obtain ⟨m, s, hs⟩ :=
      MultiplicityAdditivityProof.exists_series (hd.hasFiniteLength hn)
    exact ⟨⟨m, s, hs⟩⟩)

end SegmentProductDatum
end Langlands.PadicField.TopologicalData
