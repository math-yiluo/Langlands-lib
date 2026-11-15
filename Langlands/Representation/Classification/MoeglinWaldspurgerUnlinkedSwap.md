# Swapping unlinked segment socles in a binary product

Module `Langlands.Representation.Classification.MoeglinWaldspurgerUnlinkedSwap`. Written by
Worker 5735 for Task 5735.

* `isZelevinskySocle_singleton`: a segment socle `Z` of `Δ` is a Zelevinsky socle of the
  one-segment multisegment `{Δ}` (one-block datum, the published `singletonIso`, and
  `IsIrreducibleSubrepresentation.isIrreducibleSocle_of_irreducible`).
* `twoBlocks_isIrreducible_of_unlinked`: the two-block product of the socles of two unlinked
  segments is irreducible, by the published Zelevinsky 1980 Proposition 8.5
  (`unlinkedSocleProductIrreducibility`) for the two singleton multisegments.
* `castIso_twoBlocks_swap_of_unlinked`, `castIso_swap_of_unlinked`: hence the products in the two
  orders are isomorphic up to rank transport, from the published
  `CuspidalSupport.irreducibleLiteralTwoBlockSwapEquiv` (which needs the irreducibility); the
  binary product is identified with the two-block product by
  `BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks`.
