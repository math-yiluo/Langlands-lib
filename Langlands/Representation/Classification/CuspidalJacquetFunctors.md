# Functors on the actual cuspidal Jacquet objects

This internal construction packages two existing object assignments from
`CuspidalJacquetMultiplicityStatement` as functors. The data use an arbitrary
prime, p-adic field `F`, compatible topological data `T`, block shape `B`, and
independent field and carrier universes. There is no restriction on the total
rank or the number or sizes of the blocks beyond the existing block-shape
definition. The source is the category of smooth complex representations for
the topology supplied by `T`; the target is the algebraic representation
category of the product Levi, with the same carrier universe.

`upperFunctor` sends `A` to the published object
`upperJacquet T B A.obj`. Its map is the actual normalized Jacquet map of the
underlying intertwiner. On a quotient class it sends `[v]` to `[f(v)]`.
The existing upper action uses the inverse positive half of the full upper
block modulus.

`oppositeFunctor` sends `A` to the published object
`oppositeJacquet T B A.obj`. The helper `oppositeMap` is the existing
`Jacquet.normalizedMapOfModulus` for the actual opposite unipotent subgroup
and the actual Levi subgroup, restricted along `B.leviEquiv`. Its full modulus
is the inverse upper modulus, transported to the Levi subgroup. Thus its
normalization is the inverse positive half of the opposite full modulus,
as in the existing object definition. On quotient classes its map also sends
`[v]` to `[f(v)]`.

The identity and composition fields are proved for these concrete maps.
The two object comparison lemmas and both map evaluation lemmas are
definitional equalities. The helper map permits independent source and
target carrier universes; each functor operates at a fixed carrier universe.

The provenance is internal categorical packaging of already defined Library
objects and descended maps, rather than a new translation of a literature
assertion. This pair supplies no additivity, mono/epi preservation, finite
length, multiplicity computation, adjunction, or segment constituent theorem.
Those properties require separate statements and proofs. It changes none of
the imported definitions.

The imports use the existing cuspidal Jacquet object statement, actual
induction and Jacquet definitions, and smooth category definitions. The
construction uses no segment classification, multisegment exhaustion,
ordered special-head existence, quotient coverage, tempered block uniqueness,
square-integrable classification or exhaustion, or regular exhaustion.
