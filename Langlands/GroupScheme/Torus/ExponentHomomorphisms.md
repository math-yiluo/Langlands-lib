# Actual integral-coordinate torus maps over arbitrary schemes

This internal module constructs actual homomorphisms of standard split tori
over any scheme from integral linear maps on their character-coordinate
modules. The linear map acts contravariantly. Each target coordinate character
pulls back to the fixed-exponent character specified by that linear map.
The formula holds for every integer-coordinate character as an equality of
actual group-scheme maps.

Composition and identity agree with the corresponding contravariant linear
operations. In particular an integral linear automorphism produces an actual
torus automorphism over every scheme, with inverse obtained from the inverse
integral map. If that automorphism sends an integer character vector to its
negative, the actual torus automorphism satisfies the exact corresponding
character-inversion equation over the whole base.

The construction commutes with arbitrary scheme base change through the
canonical source and target split-torus identifications. The proof tests the
equation after each coordinate projection and uses the fixed-exponent
character base-change formula.

Over a field, applying the construction to the existing actual character map
of a given homomorphism recovers that homomorphism. A specified actual field
torus automorphism therefore gives an integral coordinate equivalence and an
actual automorphism over any base scheme. The field specialization recovers
the original specified automorphism.
Pullback along any point with that original field also recovers it through
the canonical split-torus comparisons. A supplied actual field equation
inverting a character gives the exact corresponding inversion equation for
the relative automorphism and the fixed-exponent extension of that character.

The proofs use the coordinate characters and cocharacters, their identity
decomposition, integral linear algebra, and the existing field
character-coordinate equivalence. This internal construction does not
classify all torus maps over disconnected or nonreduced bases. It supplies
relative automorphisms for transporter constructions and does not assert
existence of normalizer points, reductivity, or openness of a reductive locus.
