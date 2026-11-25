# Ring idempotents from the actual clopen group decomposition

`NormalIdempotentDecomposition.toRingDecomposition` turns the clopen
identity part of an actual group-scheme endomorphism over `Spec R` into an
idempotent element of `R`. After every ring map sending this element to
one, the endomorphism becomes the identity; after every ring map sending it
to zero, it becomes the trivial map. These assertions hold for arbitrary
commutative target rings, including nonreduced rings and the zero ring.

The existing prime-spectrum theorem supplies the idempotent whose basic
open is the given clopen identity part. A ring map sending the element to
one has spectrum contained in this part. A map sending it to zero avoids
that part and hence lies in the complementary zero part. The open immersion
lifting property factors each spectrum map through the corresponding open.
Naturality of the actual pullback comparisons then transports the map
equalities.

This is an internal consequence of the actual clopen decomposition and the
published correspondence between ring idempotents and clopen subsets of
the prime spectrum. It does not assert uniqueness from arbitrary
point-functor projection formulas or perform the restricted-point-functor
translation in the relative normal-idempotent statement.
