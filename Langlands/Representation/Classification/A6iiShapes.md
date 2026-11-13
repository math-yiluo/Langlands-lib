# Shape bookkeeping for the irreducible-product argument

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiShapes`,
namespace `Langlands.Classification.A6ii`. Internal helper for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`).

- `isMinimalRepresentative_permute_flatten`: let `e` reorder the blocks of `B.flatten S`
  and keep the order of any two blocks inside the same outer block of `B` (hypothesis
  `hstab`). Then `(B.flatten S).blockPermutation e` is a minimal representative for `B`
  against `(B.flatten S).permute e`. Proof: the coordinate criterion
  `isMinimalRepresentative_iff`. Inside one flattened block the order is kept
  (`isMinimalRepresentative_blockPermutation`). Otherwise the outer block of a
  coordinate is read off its flattened block (`ProductLeviMinimalIndex.blockIndex_eq_flatten`),
  `blockIndex_blockPermutation` moves block numbers by `e⁻¹`, and `blockIndex_monotone`
  compares the coordinates.
- `compSymmCompEquiv`: pulling back along a group equivalence and its inverse gives an
  equivalent representation.
- `count_cast`: multiplicities of real Levi twists of a test representation move along
  an equality of shapes `C = C'`, provided the twist exponents correspond under the
  cast of block indices. Proof: substitute the equality.
- `outer_composeRefinement`: under `(B.flatten Q).flatten R = B.flatten
  (B.composeRefinement Q R)`, a fine block lies in the same outer block of `B` on both
  routes. Proof: `flatten_composeRefinement_block`.
- `nonempty_flatten_iso`: the normalized product along `B.flatten S` of a family listed
  in flattened order is isomorphic to the normalized product along `B` of the blockwise
  normalized products. Proof: the published `flattenedProductInducedEquiv`.
