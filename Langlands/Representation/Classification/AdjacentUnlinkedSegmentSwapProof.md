# Adjacent unlinked segment-head swaps in a full induced product

Author: Worker 584.

`Langlands.Classification.adjacentUnlinkedSegmentSwap` proves exactly
`Langlands.Classification.AdjacentUnlinkedSegmentSwap.{uF,uV} F T`.
Its only outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
There are no additional theorem-valued hypotheses.

## Scope

With the supplied `T.topology`, for every natural rank `n`, every
`d : T.SegmentProductDatum.{max uF uV,uF} n`, supplied special heads
`hd : d.HasSegmentHeads`, and adjacent positions `j`, `j + 1` with
`h : j + 1 < d.length`, assume only that the actual segments
`d.segments ⟨j, _⟩` and `d.segments ⟨j + 1, h⟩` are not linked. For
`σ := d.shape.adjacentSwap j h`, the theorem gives

```text
Nonempty (d.induced ≅
  (T.normalizedProductInductionFunctor (d.shape.permute σ)).obj
    (fun i => d.blocks (σ i)))
```

This is an isomorphism in the category of actual smooth complex
representations of `GL_n(F)`. The new position `i` carries the supplied
original block `d.blocks (σ i)` with its exact dependent rank. Every other
block and every occurrence of a repeated segment is retained. Other pairs
may be linked, and the full product may be reducible. No order,
global nonlinkage, finite-length or whole-product irreducibility condition
is imposed. Field and carrier universes remain independent, with all
segment bases and blocks in `Type (max uF uV)`.

All natural ranks are included. An adjacent pair cannot occur at rank zero,
because every segment has positive degree and the degrees sum to `n`.
The imported constructions retain normalized induction from upper block
parabolics, positive half-modulus covariance and right translation.

## Implemented proof

Write `d₂ := AdjacentSegmentSwapLifting.mergedFiber d j h`. It is the
actual two-block datum selected from positions `j`, `j + 1` by the direct
adjacent refinement over `d.shape.adjacentMerge j h`.

1. `mergedFiber_length` gives `d₂.length = 2`.
   `mergedFiber_segments_zero` and `mergedFiber_segments_one` identify its
   two segments with precisely the original adjacent segments. Rewriting
   by these equalities transfers the sole nonlinkage premise to `d₂`.
2. `directFiber_heads d j h hd (d.shape.adjacentMergeIndex j h)` restricts
   the supplied head witnesses to these same two actual blocks.
3. The published exact theorem
   `Langlands.Classification.twoSegmentHeadCommutation.{uF,uV} F T`,
   applied to `d₂`, its length equation, those head witnesses and that
   nonlinkage premise, gives
   `Nonempty (d₂.induced ≅ (d₂.permute (d₂.shape.adjacentSwap 0 _)).induced)`.
   No commutation premise is supplied by the caller of the present theorem.
4. `AdjacentSegmentSwapLifting.lift d j h` lifts this local isomorphism to
   `Nonempty (d.induced ≅ (d.permute σ).induced)`. After extracting the
   isomorphism `e`, the proof uses the equality
   `he := SegmentProductDatum.permute_induced d σ` and returns
   `⟨e ≪≫ eqToIso he⟩`. This explicitly converts the endpoint to the
   induction-functor expression in the published target. The equality is
   definitional; this explicit composition keeps elaboration from unfolding
   the induced representation model.

The published lifting helper regroups the direct and swapped products over
the same merged outer shape, using
`Parabolic.orderedProductRegrouping.{uF,max uF uV} F T` and the exact adjacent
label bijections, rank equalities and coordinate identities. Its inner
data select the original blocks themselves. Away from the merged slot the
two inner data are equal, giving identity isomorphisms. At the merged slot
the swapped datum equals the literal two-position permutation of `d₂`.
The helper forms the family of these isomorphisms with `Pi.isoMk`, maps it
through the common outer normalized product functor, and composes with
the direct regrouping and the inverse of the swapped regrouping.

The two-factor theorem independently proves irreducibility of both orders
of the unlinked pair and constructs an actual isomorphism using
contragredient reversal. Those two-block facts impose no irreducibility
condition on the full product in this theorem. The full-product conclusion
uses actual categorical isomorphisms throughout.

## Dependencies and provenance

This is an internal categorical composition of published Library results,
not a new assertion attributed to a literature theorem. It imports the
unchanged target statement, `Classification.AdjacentSegmentSwapLifting`
and `Classification.TwoSegmentHeadCommutationProof`. The shared lifting
helper was authored by Workers 769 and 584; the independent two-factor
proof was authored by Worker 375. Their published companion Markdown
describes their own constructions and source boundaries.

The direct and transitive dependency closure was checked before reuse.
It contains no proof of generic segment-product uniqueness, ordered
conversion, square-integrable or regular exhaustion, square-integrable
Langlands classification, tempered block uniqueness, multisegment
exhaustion, ordered-head existence or quotient coverage. The imported
`SegmentGenericStatement` contains the unused uniqueness proposition
definition and its containing statement family; neither is used as a
proved input. The independent two-factor proof does not import this
full-product theorem. Thus the lower commutation input is independent of
the downstream consumers that this theorem is intended to support.
