import Langlands.Representation.Classification.SegmentHeadProductTerminalSupport
import Langlands.Representation.Classification.SegmentHeadProductContragredient

/-! Initial support witnesses obtained from derivatives of actual dual products. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear Derivative PadicField.TopologicalData
open CuspidalProductContragredient

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Original-label initial truncations and actual support multisets for the
smooth dual of a derivative constituent. -/
structure SegmentHeadProductDualInitialSupportData {n r : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} n)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) where
  truncations : Fin d.length → Option (T.Segment.{uV, uF})
  supports : Fin d.length → Multiset (T.CuspidalDatum.{uV, uF})
  initial : ∀ i, Segment.IsInitialTruncation (truncations i) (d.segments i)
  pointwise : ∀ i, {ρ | ρ ∈ supports i} = Segment.optionalSupport (truncations i)
  support : letI := T.topology
    letI := T.generalLinearTopologicalGroup r
    T.IsSupercuspidalSupport D.contragredient (∑ i, supports i)

/-- Apply terminal support to a derivative of a source subquotient of the actual
dual product, then dualize its optional truncations and support multisets. -/
def segmentHeadProductDualInitialSupportDataOfSubquotient {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n)
    (d : T.SegmentProductDatum.{uV, uF} n) (hd : d.HasSegmentHeads)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology; letI := T.generalLinearTopologicalGroup n
      SmoothRep.IsSubquotient Q d.induced.contragredient)
    (D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible)
    (hDQ : letI := T.topology
      SmoothRep.IsSubquotient D ((generalLinearDerivative T ψ n k hk).obj Q)) :
    SegmentHeadProductDualInitialSupportData T d D := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.generalLinearTopologicalGroup (n - k)
  apply Classical.choice
  have hQ' : SmoothRep.IsSubquotient Q d.dual.induced :=
    hQ.of_iso_right (d.contragredientInducedIso hd)
  obtain ⟨A, s, hA, hs, hsupport⟩ :=
    segmentHeadProductTerminalTruncationSupportOfSubquotient T ψ hn hk
      d.dual hd.dual Q hQ' D hD hDQ
  refine ⟨{
    truncations := fun i => (A i).map Segment.dual
    supports := fun i => (s i).map dualDatum
    initial := ?_
    pointwise := ?_
    support := ?_ }⟩
  · intro i
    simpa only [SegmentProductDatum.dual_segments, Segment.dual_dual] using (hA i).dual
  · intro i
    rw [Segment.optionalSupport_dual, ← hs i]
    ext ρ
    simp only [Set.mem_ofPred_eq, Multiset.mem_map, Set.mem_image]
  · have hmap : (∑ i, s i).map dualDatum = ∑ i, (s i).map dualDatum :=
      map_sum (Multiset.mapAddMonoidHom dualDatum) _ _
    change T.IsSupercuspidalSupport D.contragredient
      (∑ i : Fin d.dual.length, (s i).map dualDatum)
    rw [← hmap]
    exact isSupercuspidalSupport_contragredient.{uF, uV} hsupport

/-- The support multiset retained by the data has the expected initial-support
union, including empty options and repeated original labels. -/
theorem SegmentHeadProductDualInitialSupportData.support_union {n r : ℕ}
    {d : T.SegmentProductDatum.{uV, uF} n}
    {D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    (w : SegmentHeadProductDualInitialSupportData T d D) :
    {ρ | ρ ∈ ∑ i, w.supports i} =
      ⋃ i, Segment.optionalSupport (w.truncations i) := by
  ext ρ
  simp only [Set.mem_ofPred_eq, Multiset.mem_sum, Finset.mem_univ, true_and,
    Set.mem_iUnion]
  exact exists_congr fun i => Set.ext_iff.mp (w.pointwise i) ρ

end Langlands.Classification
