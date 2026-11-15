# Internal assembly for neighboring Speh product irreducibility

This internal module assembles the final finite-length step of the neighboring
Speh product argument. It is derived from published Library interfaces. The
head-product proposition `Langlands.Aubert.HeadProductLeadingTermStatement` is
an explicit hypothesis `hH` of the two irreducibility lemmas. The module does
not prove that proposition, and it does not prove the rectangle length bound.

## Declarations

- `exists_weakHead`: the published multisegment head exhaustion theorem
  supplies a weak Langlands quotient datum for any actual irreducible
  representation, including at rank zero.
- `exists_head`: the published multisegment head existence theorem supplies,
  at the rank equal to the degree, a weak head datum with the prescribed
  multisegment and an actual head.
- `isIrreducible_of_constituent_multisegment_eq`: if every head-labelled
  irreducible subquotient of the actual normalized product of two heads has
  the sum of the two input multisegments as its label, the product is
  irreducible.
- `isIrreducible_of_constituent_segment_length_le`: if the sum of the two input
  multisegments has all segments of a common length `l`, and every
  head-labelled irreducible subquotient has all segments of length at most
  `l`, the product is irreducible.

## Proofs

For `isIrreducible_of_constituent_multisegment_eq`, the product has finite
length by `binaryProduct_preservesFiniteLength`. The two input degrees add, so
`exists_head` gives a head `H` of the sum label. The second clause of `hH`
gives composition multiplicity one for `H`. Every other irreducible class has
multiplicity zero: a positive multiplicity makes the representative a
subquotient, head exhaustion labels it, the hypothesis gives the sum label,
and ordered head classification makes it isomorphic to `H`, contradicting the
choice of class. The composition-factor vector is therefore one irreducible
generator, and the published class-detection theorem
`isIrreducible_of_compositionFactors_eq_generator` gives actual irreducibility.

For `isIrreducible_of_constituent_segment_length_le`, suppose a head-labelled
subquotient had a label different from the sum. The third clause of `hH`,
applied with the common length `l`, gives a segment longer than `l`, which
contradicts the length bound. So every label equals the sum, and the
previous lemma applies.

## Provenance

This is a derived internal reduction. Its argument is the final step of
Badulescu (2014), proof of Theorem 1(b)(ii): a constituent of the product of
the two rectangles whose segments are no longer than `l` must be the leading
term. The implementation uses only the cited Library theorems and the
explicit hypothesis `hH`.
