# Lifting an adjacent two-block isomorphism to a full segment product

Authors: Worker 769 and Worker 584.

This internal construction is derived from the definitions in
`Classification.LanglandsData`, `Classification.SegmentProductPermutation` and
`Group.GL.AdjacentMergeShape`, and from the published regrouping theorem
`Langlands.Parabolic.orderedProductRegrouping`. It makes no new literature
assertion. It is the common lifting step of the adjacent swap results for
full segment products: the segment-head version
`Langlands.Classification.AdjacentUnlinkedSegmentSwap` and the segment-socle
version `Langlands.Classification.AdjacentUnlinkedSegmentSocleSwap`. The lifting
assumes no head, socle, linkage or irreducibility condition, and no commutation
result is assumed or proved; head and socle witnesses are only restricted to the
inner data for use by those results.

Throughout, `d : T.SegmentProductDatum.{max uF uV, uF} n` is a segment-product
datum with input carriers in `Type (max uF uV)`, and `h : j + 1 < d.length`
selects the adjacent positions `j` and `j + 1`. The field `F`, its supplied
topological data `T`, the prime `p` and the universes `uF`, `uV` are arbitrary.

## Inner data

`select d f hs` is the datum whose position `i` carries the actual segment
`d.segments (f i)` and the actual block `d.blocks (f i)`, for a map
`f : Fin r → Fin d.length` and a proof `hs` that the selected degrees sum to the
new rank. It retains the supplied blocks themselves; repeated or equal segments
stay separate positions. `select_congr` says that the datum depends only on `f`.

The published shape `d.shape.adjacentMerge j h` merges blocks `j` and `j + 1`
into one outer block and keeps every other block alone. Its refinement
`d.shape.adjacentRefinement j h` and label bijection
`d.shape.adjacentBlockEquiv j h` number the blocks of `d.shape` consecutively.
The swapped shape `d.shape.permute (d.shape.adjacentSwap j h)` has the same merged
shape, with refinement `d.shape.adjacentSwapRefinement j h` and label bijection
`d.shape.adjacentSwapBlockEquiv j h`.

- `directFiber d j h m` is `select` along `k ↦ d.shape.adjacentBlockEquiv j h ⟨m, k⟩`:
  the original blocks lying in outer block `m`, in their original order. Its shape
  is definitionally `d.shape.adjacentRefinement j h m` (`directFiber_shape`).
- `swappedFiber d j h m` is `select` along
  `k ↦ d.shape.adjacentSwap j h (d.shape.adjacentSwapBlockEquiv j h ⟨m, k⟩)`: the
  blocks of the swapped datum lying in outer block `m`, named by their original
  labels. Its shape is definitionally `d.shape.adjacentSwapRefinement j h m`
  (`swappedFiber_shape`).
- `directFiber_heads` and `directFiber_socles` restrict a family of segment-head or
  segment-socle witnesses of `d` to a direct fiber, by evaluating the original
  witness at the selected label.
- `swappedFiber_eq_of_ne`: for an outer block `m` other than the merged one
  (`m.val ≠ j`), the two inner data are equal. The fiber has length one, and its
  only label is neither `j` nor `j + 1`, so the transposition fixes it; this is the
  arithmetic of `adjacentBlockEquiv_val` and `adjacentRefinement_length_of_ne`.

## The merged two-block datum

`mergedFiber d j h` is the direct fiber at the merged outer block
`d.shape.adjacentMergeIndex j h`. It has length two (`mergedFiber_length`), and
`mergedFiber_swap_bound` is the resulting bound `0 + 1 < length`. Its labels are
`j + k` (`mergedFiber_label`), so its segment at position `0` is
`d.segments ⟨j, _⟩` and its segment at position `1` is `d.segments ⟨j + 1, h⟩`
(`mergedFiber_segments_zero`, `mergedFiber_segments_one`). Its blocks are likewise
the original blocks `j` and `j + 1`, in this order.

`swappedFiber_eq_permute` identifies the swapped fiber at the merged block with
`(mergedFiber d j h).permute ((mergedFiber d j h).shape.adjacentSwap 0 _)`, the
same two blocks in the opposite order. Both sides are `select` data, so it
suffices to compare label maps. Writing `f q` for the label
`d.shape.adjacentBlockEquiv j h ⟨mergeIndex, q⟩`, the map `f` is injective, sends
position `0` to `j` and position `1` to `j + 1`, and therefore conjugates the swap
of positions `0, 1` to the swap of labels `j, j + 1`
(`Function.Injective.swap_apply`).

## Regrouping both orders over the merged shape

`directFiber_induced` and `swappedFiber_induced` unfold the induced
representations of the fibers to the normalized product functor applied to the
selected blocks; both hold by `rfl`.

`regroup_direct` applies `Parabolic.orderedProductRegrouping.{uF, max uF uV} F T`
to the shape `d.shape`, the merged shape, the adjacent refinement, its label
bijection, the definitional rank equalities and the published coordinate identity
`d.shape.adjacent_index j h`, with the actual blocks `d.blocks`. Since the rank
equalities are `rfl`, the transported inner families are exactly the direct fibers'
blocks, and `eqToIso` of the unfolding equation gives

`Nonempty (d.induced ≅ (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj (fun m => (directFiber d j h m).induced))`.

`regroup_swapped` does the same for the swapped datum
`d.permute (d.shape.adjacentSwap j h)`, using the swapped refinement, the swapped
label bijection and `d.shape.adjacentSwap_index j h`. Its outer shape is the same
merged shape `d.shape.adjacentMerge j h`, and its inner data are the swapped
fibers.

## The lifting theorem

`fiber_iso` turns an isomorphism `hm₀` between the two orders of the merged
two-block datum,

`Nonempty ((mergedFiber d j h).induced ≅ ((mergedFiber d j h).permute ((mergedFiber d j h).shape.adjacentSwap 0 _)).induced)`,

into a family of isomorphisms `(directFiber d j h m).induced ≅ (swappedFiber d j h m).induced`:
at the merged block it rewrites by `swappedFiber_eq_permute` and uses `hm₀`;
elsewhere it rewrites by `swappedFiber_eq_of_ne` and uses the identity.

`lift` assumes only `hm₀` and concludes

`Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced)`.

It composes the direct regrouping, the image under the outer normalized product
functor `T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)` of the
fiberwise family (`Pi.isoMk`), and the inverse of the swapped regrouping. All
isomorphisms are actual isomorphisms in the category of smooth complex
representations; none is a statement about composition factors. No condition is
placed on the other segments, which may be linked or repeated.

## Dependencies

The module imports only `Classification.SegmentProductPermutation` and
`Parabolic.OrderedProductRegroupingProof`. Its transitive imports consist of the
foundational definition modules for segments, segment-product data, smooth
representations and normalized parabolic induction, together with the published
regrouping proof and its lower proofs (refined induction and tensor products,
refinement coordinates, induction transitivity). No classification, exhaustion,
uniqueness, irreducibility or commutation theorem is imported.

The lifting code was first written by Worker 584 for the segment-head swap proof
draft (task 590ffdec-5f74-4d17-95ec-9e7ca34e88de) and was generalized here to an
arbitrary isomorphism at the merged slot.
