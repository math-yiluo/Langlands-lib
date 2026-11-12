import Langlands.Representation.Classification.SegmentProductConcatenation
import Langlands.Representation.Classification.SegmentEdgeMaps
import Mathlib.Data.Multiset.Bind

noncomputable section
namespace Langlands.PadicField.TopologicalData.SegmentProductDatum
open GeneralLinear CategoryTheory
universe uF uV
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  {n : ℕ} (B : BlockShape n) (d : ∀ i, SegmentProductDatum.{max uF uV,uF} T (B.size i))

theorem concatenate_multisegment :
    (concatenate B d).multisegment = ∑ i, (d i).multisegment := by
  classical
  simp only [multisegment, concatenate_segments]
  have hflat (L : List (List (Segment.{max uF uV,uF} T))) :
      (L.flatten : Multiset (Segment.{max uF uV,uF} T)) =
        (List.map Multiset.ofList L).sum := by
    induction L with
    | nil => rfl
    | cons l L ih =>
      change (l : Multiset (Segment.{max uF uV,uF} T)) + (L.flatten : Multiset (Segment.{max uF uV,uF} T)) = _
      exact congrArg (fun s => (l : Multiset (Segment.{max uF uV,uF} T)) + s) ih
  exact (hflat (List.ofFn (fun i => List.ofFn (d i).segments))).trans (by
    rw [List.map_ofFn, List.sum_ofFn]
    rfl)

theorem concatenate_isPrecedenceOrdered
    (ho : ∀ i, (d i).IsPrecedenceOrdered)
    (hu : ∀ i j, i ≠ j → ∀ Δ ∈ (d i).multisegment,
      ∀ Δ' ∈ (d j).multisegment, ¬ Δ.IsLinked Δ') :
    (concatenate B d).IsPrecedenceOrdered := by
  apply (T.isPrecedenceOrdered_iff_list _).mpr
  rw [concatenate_segments]
  apply List.pairwise_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact (T.isPrecedenceOrdered_iff_list _).mp (ho i)
  · apply List.pairwise_ofFn.mpr
    intro i j hij Δ hΔ Δ' hΔ' hp
    exact hu i j (ne_of_lt hij) Δ hΔ Δ' hΔ' hp.isLinked

/-- Actual injection of the product of supplied strong socles into the flat product. -/
def socleProductEmbedding
    (π : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hπ : ∀ i, (d i).IsZelevinskySocle (π i)) :
    letI := T.topology
    {f : ((T.normalizedProductInductionFunctor B).obj π).representation.IntertwiningMap
      (concatenate B d).induced.representation // Function.Injective f} := by
  letI := T.topology
  let f := fun i => (hπ i).2.2.2.choose
  have hf : ∀ i, Function.Injective (f i) := fun i => (hπ i).2.2.2.choose_spec.1
  let e := concatenateInducedEquiv B d
  exact ⟨e.toIntertwiningMap.comp (T.normalizedProductInducedMap B f),
    e.injective.comp (Langlands.Classification.SegmentEdge.normalizedProductInducedMap_injective
      T B f hf)⟩

end Langlands.PadicField.TopologicalData.SegmentProductDatum
