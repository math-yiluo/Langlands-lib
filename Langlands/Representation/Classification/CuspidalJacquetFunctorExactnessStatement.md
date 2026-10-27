# Additivity and mono/epi preservation for actual Jacquet functors

`CuspidalJacquetFunctorExactnessStatement` is an internal categorical
interface for the actual functors `CuspidalJacquetMultiplicity.upperFunctor`
and `oppositeFunctor`. For every prime, p-adic field, supplied compatible
topology, rank, and block shape, it asserts six properties in this order:
upper additivity, upper preservation of monomorphisms, upper preservation
of epimorphisms, opposite additivity, opposite preservation of
monomorphisms, and opposite preservation of epimorphisms.

Both functors have source the supplied-topology smooth complex
representations of `GL_n(F)` and target the algebraic representations of
the product Levi. Field and carrier universes are independent, with the
same carrier universe in source and target. All block shapes, including
the zero-rank case, retain their existing scope.

Additivity says that the actual quotient map of a sum of intertwiners is
the sum of their quotient maps. Preservation of monomorphisms and
epimorphisms says that injective and surjective smooth intertwiners,
respectively, induce injective and surjective maps of the actual normalized
Jacquet quotients. These are the categorical instances consumed by the
published multiplicity-one constituent criteria.

The provenance is an internal repackaging of the existing upper normalized
Jacquet exactness and generic smooth coinvariant exactness mechanisms.
The statement itself supplies none of these properties as proofs.
It asserts the specified six categorical properties, rather than any
additional formulation of exactness on arbitrary sequences. It supplies no
finite length, positivity or value of a Jordan–Hölder multiplicity,
adjunction, nonzero induction map, or segment constituent.
