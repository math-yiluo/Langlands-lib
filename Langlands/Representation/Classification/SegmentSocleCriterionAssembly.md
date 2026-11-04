# Conditional assembly of the segment socle irreducibility criterion

Authors: Worker 250, with lifting code by Worker 769 and Worker 584 (see
"Credits").

This module derives the irreducibility criterion for products of segment socles,
`Langlands.Classification.SegmentSocleProductIrreducibility.{uF, uV} F T`
(Zelevinsky 1980, Theorem 4.2, in socle form), from three published proposition
definitions. They are supplied as explicit hypotheses:

- `h1 : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T`: a product of
  segment socles over an unlinked multisegment is irreducible (the sufficient
  direction of Theorem 4.2).
- `h3 : LinkedSegmentSoclePairReducible.{uF, uV} F T`: for a datum of length two
  with segment socles whose two segments are linked, the product is not
  irreducible (Zelevinsky 1980, the reducibility part of Proposition 4.6 and its
  consequence for the other order).
- `h19 : TwoFactorProductConstituentCommutativity.{uF, max uF uV} F T`: for two
  irreducible smooth factors, the products in the two orders have the same
  Jordan–Hölder factors (Zelevinsky 1980, Theorem 1.9, irreducible two-factor
  case).

The first two are in `Classification.SegmentSocleCriterionHalvesStatement`, the
third is in `Classification.TwoFactorProductConstituentCommutativityStatement`.
No proof of any of them is used or claimed here. The module is therefore a
conditional assembly. It is not a proof of the criterion, and a proof of the
criterion is obtained only by applying `segmentSocleProductIrreducibility_of_halves`
to published proofs of the three hypotheses. The module
`Classification.SegmentSocleProductIrreducibilityProof` does exactly this.

## Provenance

The module is internal: it makes no new literature assertion beyond the
implication from the three hypotheses to the criterion. Zelevinsky reduces the
implication "irreducible ⇒ unlinked" of Theorem 4.2 to the reducibility of
`⟨Δ⟩ × ⟨Δ'⟩` for linked segments `Δ`, `Δ'`, in one sentence (§4.6, printed
p. 185). The details of that reduction are implemented here as follows. A linked
pair at adjacent positions makes the whole product reducible, by `h3` and the
regrouping of the product around that pair. A linked pair at a larger distance is
moved to adjacent positions by interchanging adjacent unlinked socles, using `h19`
and `h1` for two factors. The sufficient direction is the hypothesis `h1`
unchanged.

Throughout, `p` is an arbitrary prime, `F : PadicField.{uF} p` an arbitrary
field with supplied topological data `T`, and segments live in the arbitrary
universe `uV`. Blocks have carriers in `Type (max uF uV)`, as in
`T.SegmentProductDatum.{uV, uF}`. Repeated and equal segments stay separate
positions, and every ordering is allowed.

## Elementary facts on irreducible representations

For a monoid `G` and complex representations:

- `top_ne_bot_iff`: `(⊤ : Subrepresentation ρ) ≠ ⊥` exactly when the carrier is
  nontrivial.
- `nontrivial_of_isIrreducible`: an irreducible representation has a nonzero
  carrier, since `IsIrreducible` includes nontriviality of the subrepresentation
  lattice.
- `exists_proper_of_not_isIrreducible`: a reducible representation with a nonzero
  carrier has a subrepresentation different from `⊥` and `⊤`.
- `not_isIrreducible_of_proper`: conversely, such a subrepresentation rules out
  irreducibility.
- `toGraded`, `toGraded_bijective`, `toGradedEquiv`: a representation is
  equivalent to the only graded quotient of a one-step object filtration, by the
  graded projection from the last (top) step.
- `nonempty_equiv_of_haveSameJordanHolderFactors`: if `ρ` is irreducible and
  `HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ)`, then `ρ` and `σ` are
  equivalent. The witnessing filtrations have simple factors and the same length.
  That length is `repLength (Rep.of ρ).ρ = 1` (`repLength_eq_of_hasSimpleFactors`,
  `repLength_eq_one_iff`). The two one-step filtrations then give
  `ρ ≃ gr₀ ≃ gr₀' ≃ σ`.

## Segment-product data

- `isIrreducible_of_isSegmentSocle`: a segment socle is irreducible (the first
  part of `IsIrreducibleSocle`).
- `rank_pos`, `length_pos`: a datum has positive rank exactly when it has a
  segment, since segment degrees are positive.
- `induced_nontrivial`: if all blocks are nonzero and the rank is positive, the
  product `e.induced` is nonzero. Worker 494's published
  `Parabolic.normalizedProductSlotSubrepresentation_ne_bot` is applied to the
  slot `0` and the subrepresentation `⊤`, together with
  `normalizedProductSlotSubrepresentation_top`.
- `induced_nontrivial_of_socles`: the same for segment-socle blocks.
- `permute_multisegment`: reindexing a datum keeps its multisegment.
- `adjacentSwap_apply_val`: the values of `B.adjacentSwap j h`. It sends `j` to
  `j + 1`, sends `j + 1` to `j`, and fixes every other position.

## Adjacent regrouping for an unsaturated segment universe

The published `Classification.AdjacentSegmentSwapLifting` (Workers 769 and 584)
treats only `T.SegmentProductDatum.{max uF uV, uF}`, whose segments lie in the
carrier universe. The criterion has segments in an arbitrary universe `uV`, so
the construction is restated here for `T.SegmentProductDatum.{uV, uF}`. The
blocks still have carriers in `Type (max uF uV)`, which is the universe of the
published regrouping theorem `Parabolic.orderedProductRegrouping.{uF, max uF uV}`.
The declarations and their proofs follow that module:

- `select d f hs` is the datum carrying the actual segments `d.segments (f i)`
  and actual blocks `d.blocks (f i)`. `select_congr` says that it depends only on
  `f`.
- For `h : j + 1 < d.length`, `directFiber d j h m` and `swappedFiber d j h m`
  are the inner data of the direct and the swapped order over the common merged
  shape `d.shape.adjacentMerge j h`. `mergedFiber d j h` is the direct fiber at
  the merged slot. It has length two (`mergedFiber_length`), its segments are
  `d.segments ⟨j, _⟩` and `d.segments ⟨j + 1, h⟩`
  (`mergedFiber_segments_zero`, `mergedFiber_segments_one`), and its blocks are
  the original blocks `j` and `j + 1`.
- `directFiber_socles` restricts segment-socle witnesses to a direct fiber.
- `swappedFiber_eq_of_ne`: away from the merged slot the two fibers are equal.
  `swappedFiber_eq_permute`: at the merged slot, the swapped fiber is the
  two-block permutation of `mergedFiber d j h`.
- `regroup_direct` and `regroup_swapped`: `d.induced` and
  `(d.permute (d.shape.adjacentSwap j h)).induced` are isomorphic to the outer
  normalized product over the merged shape of the direct, respectively swapped,
  fibers. They apply `Parabolic.orderedProductRegrouping`.
- `fiber_iso` and `lift`: an isomorphism between the two orders of the merged
  two-block datum lifts to an actual isomorphism
  `d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced`.

The new declaration in this section is `mergedFiber_isIrreducible`. If the blocks
of `d` are segment socles and `d.induced` is irreducible, then the merged
two-block product `(mergedFiber d j h).induced` is irreducible. Otherwise it is
nonzero (`induced_nontrivial_of_socles`), so it has a proper nonzero
subrepresentation `S`. All other fibers are nonzero products of socles. Worker
494's published `Parabolic.normalizedProductSlotSubrepresentation_proper_nonzero`
lifts `S` to a proper nonzero subrepresentation of the outer product over the
merged shape. That product is isomorphic to `d.induced` by `regroup_direct`, so
`d.induced` would be reducible (`LengthTwo.isIrreducible_of_equiv`).

## The local steps

- `isIrreducible_of_unlinked`: `h1` stated at an arbitrary positive rank `m`
  instead of `n + 1`.
- `pair_swap_iso`: let `e` be a datum of length two with segment socles whose
  two segments are not linked. Then `e.induced` is isomorphic to its two-block
  permutation. The multisegment of `e` is unlinked, since a segment is never
  linked to itself. Hence `e.induced` is irreducible by `h1`. By `h19`, the two
  orders have the same Jordan–Hölder factors. An irreducible representation with
  the same factors as another is equivalent to it
  (`nonempty_equiv_of_haveSameJordanHolderFactors`), and `SmoothRep.mkIso` turns
  the equivalence into an isomorphism.
- `swap_iso`: adjacent unlinked socles in a full product may be interchanged, by
  `pair_swap_iso` at `mergedFiber d j h` and `lift`.
- `adjacent_not_isLinked`: in an irreducible product of socles, adjacent segments
  are not linked. If they were, `h3` would make the merged two-block product
  reducible, contradicting `mergedFiber_isIrreducible`.

## The induction on the distance

`not_isLinked_of_isIrreducible h1 h3 h19 k` states the following. For every datum
`d` with segment socles and irreducible `d.induced`, the segments at positions
`i` and `i + k + 1` are not linked. The proof is by induction on `k`,
generalizing over the datum and the rank.

- `k = 0` is `adjacent_not_isLinked`.
- For `k + 1`: the segments at `i` and `i + 1` are not linked by
  `adjacent_not_isLinked`. `swap_iso` then gives
  `d.induced ≅ (d.permute (d.shape.adjacentSwap i _)).induced`, so the permuted
  datum also has segment socles and an irreducible product. In the permuted
  datum, position `i + 1` carries the old segment `i`, and position
  `i + 1 + k + 1` carries the old segment `i + (k + 1) + 1`
  (`adjacentSwap_apply_val`). The induction hypothesis at position `i + 1` of the
  permuted datum is the claim.

## The criterion

`segmentSocleProductIrreducibility_of_halves h1 h3 h19 :
SegmentSocleProductIrreducibility.{uF, uV} F T`. For `d` with segment socles:

- If `d.induced` is irreducible, take two segments of `d.multisegment`. They are
  `d.segments a` and `d.segments b` for positions `a`, `b`. If `a = b` they are
  not linked (`Segment.not_isLinked_self`). Otherwise apply
  `not_isLinked_of_isIrreducible` with the smaller position and the distance
  minus one, using `IsLinked.symm` when `b < a`. Hence `d.multisegment` is
  unlinked.
- If `d.multisegment` is unlinked, `h1` gives irreducibility.

The universe instance `h19.{uF, max uF uV}` is the one matching the block
carriers `Type (max uF uV)` of `T.SegmentProductDatum.{uV, uF}`.

## Dependencies and independence

The module imports only:

- the statement modules `Classification.SegmentGenericStatement` (the target),
  `Classification.SegmentSocleCriterionHalvesStatement` and
  `Classification.TwoFactorProductConstituentCommutativityStatement`
  (proposition definitions only);
- the definitions `Classification.SegmentProductPermutation`;
- the published regrouping proof `Parabolic.OrderedProductRegroupingProof`;
- Worker 494's published slot lift `Parabolic.ProductInductionSubrepresentation`;
- the length and length-two APIs `Filtration.RepresentationLength` and
  `Filtration.LengthTwoMatching`.

The proof modules in its transitive closure are lower infrastructure:
filtrations and Jordan–Hölder transport, length criterion, smooth and compact
induction, parabolic refinement, regrouping, tensor and factor-matching results,
twists and admissibility. No classification, exhaustion, existence, coverage,
uniqueness, commutation or swap theorem is imported. In particular, the module
does not use any of the following: `TwoSegmentSocleCommutation` (tasks 426911b4,
66e3b87c), `AdjacentUnlinkedSegmentSocleSwap`, `AdjacentSegmentSwapLifting`
(its code is restated instead), the special-head criterion (task 8364e73f), task
e3634665, OrderedMultisegmentSocleExistence, task 23189526, socle exhaustion
f3a69bc8, segment analytic classification aca8805b, or the exclusions 3bfb61fa,
ebea9a8a, 20e4e1c6, 52e97845, 1cb45da2, cd8ab97c and bf433f0a of task 2ae5cbe5.

## Credits

The lifting part (`select` through `lift`) was written by Worker 584 and Worker
769 in `Classification.AdjacentSegmentSwapLifting`. Worker 250 restated it for
the segment universe `uV` and wrote the rest of the module.
