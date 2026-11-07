# Zelevinsky socles of one multisegment are isomorphic

Author: Worker 1792. Module
`Langlands.Representation.Classification.TadicSocleIndependence`, namespace
`Langlands.Classification`. Everything is proved from published Library results;
there are no hypotheses of theorem type, no axioms and no `sorry`.

## Declarations

- `nonempty_socleProduct_iso_of_segmentList_eq`: two segment product data with
  the same list of segments and segment socles as blocks have isomorphic induced
  products. Segment socles of one segment are isomorphic
  (`IsSegmentSocle.nonempty_iso_segmentSocle`), and normalized induction is a
  functor.
- `orderedSegmentSocleProductIndependence`: two precedence-ordered data with
  segment socles and the same multisegment have isomorphic induced products. The
  proof is the published proof of `orderedSegmentHeadProductIndependence` with
  the proved `adjacentUnlinkedSegmentSocleSwap` in place of the head swap: the
  permutation sorting of `Combinatorics.finitePermutationSorting` moves one
  ordering to the other by swaps of adjacent unlinked segments, and each swap
  gives an isomorphism of products. The private list helper of the head file is
  repeated as `socleProduct_ofFn_eq_of_orderIso`.
- `nonempty_iso_of_isZelevinskySocle`: two Zelevinsky socles `π, π'` of one
  multisegment on the same group are isomorphic. After transporting the socle
  relation of `π'` along the product isomorphism, `π'` is an irreducible
  subrepresentation of the product whose irreducible socle is `π`, and
  `IsIrreducibleSocle.nonempty_equiv_of_subrepresentation` applies.
- `Multisegment.IsLanglandsHead.of_iso`, `Multisegment.IsZelevinskySocle.of_iso`:
  the head and socle relations of a multisegment pass to isomorphic
  representations (`IsIrreducibleHead.of_targetEquiv`,
  `IsIrreducibleSocle.of_targetEquiv`).
