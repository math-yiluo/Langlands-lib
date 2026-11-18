# Unipotence from schematically dense rational points

`Langlands.GroupScheme.perfectFieldUnipotentRationalPoints` proves
`Langlands.GroupScheme.PerfectFieldUnipotentRationalPointsStatement.{u}`,
which encodes Milne (2017), Corollary 14.10. See the
[statement and source comparison](RationalPointsStatement.md).

The forward implication reindexes each representation by `Fin` of the
cardinality of its index set and applies the published uniform product bound
to the difference from the identity. The global-sections isomorphism of
`Spec k` carries the nilpotence identity to the rational matrix.

The linear algebra for the converse extends scalars to an algebraic closure
and chooses a minimal nonzero invariant subspace. The action on this
subspace is irreducible, and each acting endomorphism has the trace of the
identity because its difference from the identity is nilpotent. For each
acting endomorphism `A`, the linear functional `T ↦ tr((A - 1) * T)` vanishes
on the action's image by multiplicativity. Burnside's span theorem and the
nondegenerate matrix trace pairing give `A = 1`. Applying a `k`-linear
functional on the algebraic closure to each coordinate of a nonzero fixed
vector gives a nonzero rational fixed vector. The functional is chosen to
be nonzero on one of the vector's coordinates.

For each matrix representation, the coordinate differences for the
universal fixed-vector equation vanish on all rational points. Schematic
density makes each closed vanishing subscheme the whole group. This gives
fixedness on every test scheme, which is the defining condition of
`IsUnipotent`. See the [schematic-density lemma](RationalFixedVector.md).
