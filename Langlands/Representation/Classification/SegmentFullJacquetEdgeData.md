# Edge data for the full cuspidal Jacquet modules of segment constituents

Author: Worker 964.

Module `Langlands.Representation.Classification.SegmentFullJacquetEdgeData`,
namespace `Langlands.SegmentFullJacquet`. This is an internal helper for the proof
of `Langlands.Classification.SegmentFullJacquetFormula`. It assembles both clauses
from the conditional clauses of `SegmentFullJacquetAssembly` and the published edge
modules of Worker 890.

Notation:
- `β = BlockShape.uniform m r hr` and `γ = β.adjacentMerge k hk`, which merges
  blocks `k` and `k + 1`;
- `kk = β.adjacentMergeIndex k hk`, the merged slot;
- `σ = T.segmentFactors A m hr`;
- `slotFamily T β k hk σ`, the family of slot products `i_{S_j}(σ_{e(j,·)})` from the
  published `SegmentEdgeMaps`.

## Definitions

Both are abbreviations of families that the published edge modules already use.
They introduce no new mathematics.

- `quotientEdgeFamily F T hr A k hk W`: for an invariant subspace `W` of the merged
  slot product, the family `slotFamily T β k hk σ` with slot `kk` replaced by the
  quotient by `W` (`Function.update` with `SmoothRep.quotient`).
- `subEdgeFamily F T hr A k hk W`: the same family with slot `kk` replaced by `W`
  itself (`SmoothRep.subrepresentation`).

## Results

- `hedgeSub_of`. Hypotheses: `hE : SegmentEdgeJacquetFiltration` (at universe
  `max uF uV` for the edge family), a supercuspidal `A` of `GL_r`, `k` with
  `k + 1 < β.length`, and `W`. Assume (H1) and (H2) of the edge filtration for
  `quotientEdgeFamily`:
  - (H1) is the published `FamilyJacquetVanishing`;
  - (H2) is the published `FamilyJacquetEquiv`, against the factors with `k` and
    `k + 1` exchanged (`adjacentSwap k hk`).

  Then the edge filtration and the published surjection `segmentEdgeQuotientMap`
  give the edge data of `subrepresentation_jacquet_equiv`:
  - a family `Y` on `γ` and a filtration of the `β`-Jacquet module of `i_γ(Y)`;
  - its graded pieces are the transports of the swapped segment tensor, indexed by
    the minimal permutations keeping `k` before `k + 1`;
  - a surjection `i(σ) → i_γ(Y)`.
- `hedgeQuot_of`. The same with `subEdgeFamily`, (H2) against `σ` itself, and the
  published injection `segmentEdgeSubMap`. This gives the edge data of
  `quotient_jacquet_equiv`, with an injection `i_γ(Y) → i(σ)`.
- `segmentFullJacquetFormula_of`. Assume:
  - `hassoc`, the associated Jacquet filtration
    `AssociatedJacquetFiltrationTheorem F T n` in every rank `n`;
  - `hE`, the edge filtration;
  - `hgeo : PadicGeometricLemmaTheorem.{uF, uV}`;
  - `hcomp` and `hjac`, the adjacent composition and Jacquet clauses of Ze80
    1.11(b) (`TwoSupercuspidalAdjacentProductComposition` and
    `TwoSupercuspidalAdjacentProductJacquet`).

  Then `SegmentFullJacquetFormula F T` holds. Take a segment `Δ` and a
  representative `A` of its base. The published `isSegmentSubrepresentation_iff`
  and `isSegmentQuotient_iff` restate the hypothesis on `π` with this `A`, with
  `m = Δ.length` and `r = Δ.rank`. For every edge `k`, the published
  `segment_updateQuotient_hypotheses` (respectively
  `segment_updateSubrepresentation_hypotheses`) supplies `W` with (H1) and (H2)
  from `hgeo`, `hcomp` and `hjac`. Then `hedgeSub_of` (respectively
  `hedgeQuot_of`) gives the edge data, and `subrepresentation_jacquet_equiv`
  (respectively `quotient_jacquet_equiv`) gives the clause.
- `segmentFullJacquetFormula_of_prerequisites`. Assume:
  - `hassoc` as above;
  - `hgeo : PadicGeometricLemmaTheorem.{uF, uV}`;
  - `hgeo' : PadicGeometricLemmaTheorem.{uF, max uF uV}`;
  - `h111 : TwoSupercuspidalProductStructure F T` (Ze80 1.11).

  Then `SegmentFullJacquetFormula F T` holds. The edge filtration `hE` is the
  published `segmentEdgeJacquetFiltration_of_padicGeometricLemma` applied to
  `hgeo'`; the geometric lemma is needed in universe `max uF uV` because the edge
  families live there. `hcomp` and `hjac` are the second and third components of
  `h111`.

The final proof module applies `segmentFullJacquetFormula_of_prerequisites` to the
published proofs of its hypotheses.
