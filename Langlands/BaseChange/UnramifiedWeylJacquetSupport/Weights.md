# Exactness of integral diagonal generalized weights

An intertwiner of tuples of linear operators intertwines powers of the
operators after scalar subtraction. It therefore preserves the intersections
of their maximal generalized eigenspaces. An injective intertwiner also
reflects membership in these intersections. For a surjective intertwiner
from a finite-dimensional space, decompose a lift into its component of the
specified joint weight and its component in the sum of the other weights.
Independence of the target weight spaces makes the second component map to
zero when the target vector has the specified weight. Consequently the
restricted maps preserve short exact sequences. Rank–nullity gives
additivity of the weight dimensions.

The integral diagonal is compact because the Borel Levi embeds as a closed
subgroup and the spherical subgroup is compact. On smooth Levi
representations, averaging over the integral diagonal lifts fixed vectors
across surjections. An injective intertwiner reflects fixedness. Combining
these facts with joint weight exactness proves
`finrank_torusWeightSpace_exact`.

Normalized Jacquet maps preserve smooth subrepresentations and quotients
through injectivity and surjectivity of the corresponding unipotent
coinvariant maps. Restriction to the integral diagonal fixed space and to
each joint weight gives the subquotient bound
`borelJacquetMultiset_le_of_subquotient`. The same restrictions carry a
Jacquet equivalence to an isomorphism on each weight space, so
`borelJacquetMultiset_eq_of_equiv` also applies across carrier universes.
