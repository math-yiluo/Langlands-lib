# Global unit coboundaries from trivial module Picard groups

This internal derived module combines the published effectivity theorem for
natural unit cocycles with the published affine line-bundle trivialization
obtained from `Subsingleton (CommRing.Pic R)`.

For an affine, flat, surjective morphism `p : X → Spec R`, a natural,
multiplicative family of units on all equal-composite pairs is a coboundary of
one global unit on `X`. The proof descends the family to a line bundle with a
trivialized pullback, trivializes that line bundle using module Picard
triviality, and compares the two trivializations. The inverse of the scalar of
their difference has the convention `c(a,b) = a*(q) · b*(q)⁻¹`.

`unitCoboundaryOfPicTrivial` chooses such a unit from the proved existence
theorem. Its `_spec` lemma gives the displayed coboundary equation on every
test scheme and every equal-composite pair. The choice is not claimed to be
canonical or unique.

The auxiliary comparison formula states that changing a pullback
trivialization by a structure-sheaf automorphism changes the comparison by
the inverse automorphism pulled back along the first map and the automorphism
pulled back along the second. Its proof expands the canonical comparisons
and cancels inverse isomorphisms.

The result is uniform over arbitrary commutative rings, including the zero
ring, with no Noetherian or local finite presentation hypothesis.
