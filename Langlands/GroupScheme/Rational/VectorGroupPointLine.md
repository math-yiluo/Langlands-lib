# An additive one-parameter subgroup through a vector-group point

Given an actual group scheme `V` over a field `k : Type u`, natural vector
coordinates of dimension `n` on every scheme test, and an actual rational point
`y` of `V`, `RelativeRoot.pointLineHom` constructs an actual homomorphism from
`VectorGroup.groupScheme k 1` into `V`. Its value at additive coordinate one is
exactly `y`, as proved by `pointLineHom_at_one`. The corollary
`IsVectorGroupOfDimension.exists_pointLine` packages existence directly from
the Library's actual vector-group predicate. The field and characteristic are
unrestricted and `n = 0` is permitted; the morphism may be trivial.

This is a derived coordinate construction. On a test scheme `T`, pull the
rational point `y` back along the unique map from `T` to the base test. Multiply
each of its vector coordinates by the single additive input coordinate, and
apply the inverse vector-coordinate equivalence. Distribution over addition
makes this a homomorphism of point groups. Naturality of the supplied vector
coordinates, naturality of the standard additive coordinate and multiplicativity
of pullback of global functions give naturality on all scheme tests, including
nonreduced ones. The group-valued Yoneda construction `homOfPoints` turns this
family into the actual group-scheme homomorphism.

At the original rational test and coordinate one, multiplication by one leaves
the coordinates of the constant point unchanged. The map from the base test to
itself is the identity, so that point is `y`. Injectivity of the coordinates
proves the exact image equation in the `rationalPoints.map` convention. This
adapter does not assert that a general commutative or unipotent group is a vector
group; the existing all-test vector-group hypothesis supplies that input.
