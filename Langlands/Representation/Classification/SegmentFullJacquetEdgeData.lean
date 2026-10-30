import Langlands.Representation.Classification.SegmentFullJacquetAssembly
import Langlands.Representation.Classification.SegmentEdgeMaps
import Langlands.Representation.Classification.SegmentEdgeFamilyHypotheses
import Langlands.Representation.Classification.SegmentEdgeJacquetReduction
import Langlands.Representation.Classification.SegmentFullJacquetStatement

/-!
# Edge data for the full cuspidal Jacquet modules of segment constituents

The edge representations of the segment induction are the products
`i_γ(…, Y_kk, …)` over the shape `γ` merging blocks `k` and `k + 1`, with a
subrepresentation or quotient `Y_kk` of the merged slot product. Their Jacquet
filtrations come from the published `SegmentEdgeJacquetFiltration`, and their maps
to and from the segment induction from the published edge maps. This module
packages these data in the form used by the conditional clauses, and assembles
both clauses for every segment from the associated Jacquet filtration, the
geometric lemma and Ze80 1.11.
-/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Geometric CuspidalSupport Classification Classification.SegmentEdge

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The edge family of the segment induction with the quotient by `W` in the
merged slot: slot `j` of `γ = β.adjacentMerge k hk` carries the slot product of
`β = (r, …, r)`, except the merged slot, which carries its quotient by `W`. -/
abbrev quotientEdgeFamily {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk
        (T.segmentFactors A m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
      (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier) :=
  letI := T.topology
  Function.update (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr))
    ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
    (SmoothRep.quotient (slotFamily T (BlockShape.uniform m r hr) k hk
      (T.segmentFactors A m hr) ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)

/-- The edge family of the segment induction with `W` itself in the merged slot. -/
abbrev subEdgeFamily {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk
        (T.segmentFactors A m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
      (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier) :=
  letI := T.topology
  Function.update (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr))
    ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
    (SmoothRep.subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk
      (T.segmentFactors A m hr) ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)

/-- The edge data of the subrepresentation clause from the published Jacquet
filtration of edge representations and the published surjection of the segment
induction onto the edge representation with a quotient in the merged slot. -/
theorem hedgeSub_of
    (hE : SegmentEdgeJacquetFiltration.{uF, uV, max uF uV} F T)
    {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk
        (T.segmentFactors A.obj m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation)
    (h1 : FamilyJacquetVanishing T hr k hk (quotientEdgeFamily F T hr A.obj k hk W))
    (h2 : FamilyJacquetEquiv T hr k hk
      (fun i => T.segmentFactors A.obj m hr (adjacentSwap k hk i))
      (quotientEdgeFamily F T hr A.obj k hk W)) :
    letI := T.topology
    ∃ (Y : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
          (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier))
      (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier)
          (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) //
        IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
          (BlockShape.uniform m r hr) v.val.val})
      (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
        (BlockShape.uniform m r hr)).obj ((T.normalizedProductInductionFunctor
          ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y)).representation) N),
      (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport _ _ (e i).val.val.val (e i).val.property
          (FiniteTensor.externalSmoothObject (fun i =>
            T.segmentFactors A.obj m hr (adjacentSwap k hk i))).representation))) ∧
      ∃ q : (T.segmentInduced A.obj m hr).representation.IntertwiningMap
          ((T.normalizedProductInductionFunctor
            ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y).representation,
        Function.Surjective q := by
  let := T.topology
  obtain ⟨N, e, s, hs⟩ := hE m r hr k hk
    (fun i => T.segmentFactors A.obj m hr (adjacentSwap k hk i))
    (quotientEdgeFamily F T hr A.obj k hk W) h1 h2
  exact ⟨_, N, e, s, hs, SmoothRep.hom (segmentEdgeQuotientMap T A.obj m hr k hk W),
    segmentEdgeQuotientMap_surjective T A.obj m hr k hk W⟩

/-- The edge data of the quotient clause from the published Jacquet filtration of
edge representations and the published injection into the segment induction of
the edge representation with a subrepresentation in the merged slot. -/
theorem hedgeQuot_of
    (hE : SegmentEdgeJacquetFiltration.{uF, uV, max uF uV} F T)
    {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk
        (T.segmentFactors A.obj m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation)
    (h1 : FamilyJacquetVanishing T hr k hk (subEdgeFamily F T hr A.obj k hk W))
    (h2 : FamilyJacquetEquiv T hr k hk (T.segmentFactors A.obj m hr)
      (subEdgeFamily F T hr A.obj k hk W)) :
    letI := T.topology
    ∃ (Y : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
          (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier))
      (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier)
          (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) //
        IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
          (BlockShape.uniform m r hr) v.val.val})
      (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
        (BlockShape.uniform m r hr)).obj ((T.normalizedProductInductionFunctor
          ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y)).representation) N),
      (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport _ _ (e i).val.val.val (e i).val.property
          (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation))) ∧
      ∃ ι : ((T.normalizedProductInductionFunctor
            ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y).representation.IntertwiningMap
          (T.segmentInduced A.obj m hr).representation,
        Function.Injective ι := by
  let := T.topology
  obtain ⟨N, e, s, hs⟩ := hE m r hr k hk (T.segmentFactors A.obj m hr)
    (subEdgeFamily F T hr A.obj k hk W) h1 h2
  exact ⟨_, N, e, s, hs, SmoothRep.hom (segmentEdgeSubMap T A.obj m hr k hk W),
    segmentEdgeSubMap_injective T A.obj m hr k hk W⟩

/-- Both full cuspidal Jacquet formulas, conditional on the associated Jacquet
filtration in every rank, the Jacquet filtration of edge representations, the
geometric lemma, and the two adjacent clauses of Ze80 1.11(b). -/
theorem segmentFullJacquetFormula_of
    (hassoc : ∀ n, AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hE : SegmentEdgeJacquetFiltration.{uF, uV, max uF uV} F T)
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (hcomp : TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T)
    (hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T) :
    SegmentFullJacquetFormula.{uF, uV} F T := by
  let := T.topology
  refine ⟨?_, ?_⟩
  · intro Δ A π hA hπ
    exact subrepresentation_jacquet_equiv F T (hassoc _) Δ.length_pos Δ.rank_pos A
      (fun k hk => by
        obtain ⟨W, h1, h2⟩ :=
          segment_updateQuotient_hypotheses T Δ.rank_pos k hk hgeo hcomp hjac A
        exact hedgeSub_of F T hE Δ.rank_pos A k hk W h1 h2)
      π ((T.isSegmentSubrepresentation_iff Δ π A hA).mp hπ)
  · intro Δ A π hA hπ
    exact quotient_jacquet_equiv F T (hassoc _) Δ.length_pos Δ.rank_pos A
      (fun k hk => by
        obtain ⟨W, h1, h2⟩ :=
          segment_updateSubrepresentation_hypotheses T Δ.rank_pos k hk hgeo hcomp hjac A
        exact hedgeQuot_of F T hE Δ.rank_pos A k hk W h1 h2)
      π ((T.isSegmentQuotient_iff Δ π A hA).mp hπ)

/-- Both full cuspidal Jacquet formulas from the associated Jacquet filtration in
every rank, the geometric lemma in the universes `uV` and `max uF uV` of the
representation spaces, and Ze80 1.11. The edge filtration comes from the published
`segmentEdgeJacquetFiltration_of_padicGeometricLemma`. -/
theorem segmentFullJacquetFormula_of_prerequisites
    (hassoc : ∀ n, AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (hgeo' : PadicGeometricLemmaTheorem.{uF, max uF uV})
    (h111 : TwoSupercuspidalProductStructure.{uF, uV} F T) :
    SegmentFullJacquetFormula.{uF, uV} F T :=
  segmentFullJacquetFormula_of F T hassoc
    (segmentEdgeJacquetFiltration_of_padicGeometricLemma.{uF, uV, max uF uV} F T hgeo')
    hgeo h111.2.1 h111.2.2

end Langlands.SegmentFullJacquet
