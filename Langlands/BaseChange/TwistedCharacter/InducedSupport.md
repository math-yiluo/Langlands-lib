# Supercuspidal supports of the constituents of normalized products

Over a `p`-adic field `E` with topological data `T`, this module shows
that a normalized product of irreducible blocks has one supercuspidal
support shared by all its irreducible subquotients.

- `nonempty_cuspidalProduct_flatten_iso`: let `B` be a shape whose blocks
  carry cuspidal data `ρ i` with supercuspidal representations `A i j`.
  The normalized product over `B` of the supercuspidal products
  `T.cuspidalProductInduced (ρ i) _ (A i)` is isomorphic to the
  supercuspidal product of the concatenated data over the flattened
  shape. The proof is `Parabolic.orderedProductRegrouping` (induction in
  stages), with rank casts handled by a private identity isomorphism.
- `exists_supercuspidalSupport_of_normalizedProduct`: take irreducible
  blocks `Ξ i` with carrier in universe `max v z`. There is a multiset
  `s` of cuspidal data such that every irreducible subquotient `D` of the
  normalized product has supercuspidal support `s`
  (`T.IsSupercuspidalSupport D s`). The proof has three steps.
  1. Embed each block into a supercuspidal product
     (`glSupercuspidalEmbedding`).
  2. Normalized induction preserves injectivity
     (`SegmentProductCuspidalEmbedding.normalizedProductInducedMap_injective`),
     so the normalized product embeds into the normalized product of the
     supercuspidal products. By the previous lemma, that is one flat
     supercuspidal product.
  3. Every irreducible subquotient of the original product is therefore a
     subquotient of the flat supercuspidal product, and `s` is the
     concatenated cuspidal data.

The embedding of an irreducible representation into a supercuspidal
product is Bernstein–Zelevinsky (1977), Theorem 2.5. The supercuspidal
support of the constituents of a supercuspidal product is that of
Zelevinsky (1980), §1.10. The Library uses the resulting constancy to
place all constituents of a proper induction on the same side of a
selection by supercuspidal support.
