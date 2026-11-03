# Rational normalized Jacquet transitivity

This internal construction supplies the actual normalized Jacquet natural
isomorphism for nested rational standard parabolics over a nonarchimedean local
field. Put `K = leviIndex J I`, where `J` is a finite set of simple roots and
`I : Finset J`. The source is the actual `jacquetFunctor` at `J`, followed by
`leviNormalizedJacquetFunctor` for the literal standard decomposition at `K`
inside `M_J`; the target is the actual `jacquetFunctor` at `K`. The inner
functor includes the canonical subgroup equivalence from its literal
inside-Levi group to the ambient fine Levi. The field universe `u` and carrier
parameter `v` remain independent, with carriers in `max (u + 1) v`.

`standardJacquetStagesIso_of_standardProjection` retains the existing
`StandardLeviIntersectionStatement` and `StandardCocharacterStatement`,
connected reductivity, a maximal split torus and generic cocharacter. It uses
the canonical rational-point `pointTopology`, local compactness and the
nonarchimedean group property, closed ambient radicals, continuous standard
projections, closedness of the coarse Levi, and the compact-limit property of
`U_K.subgroupOf M_J`. It applies the published `standardJacquetStagesIso`,
discharging its positive Haar-character product premise with
`standardJacquetModulus_stages`. In particular, this construction assumes no
modulus identity or normalized-functor composition identity.

`standardJacquetStagesIso_of_premises` supplies the same natural isomorphism
using the topological premises of the rational involutivity reduction. With
the additional Hausdorff assumption, closed ambient parabolics and the
compact-limit property of each ambient radical, `levi_isClosed` derives
closedness of `M_J` from its continuous projection.
`isLimitOfCompactSubgroups_leviUnipotent` derives the required compact-limit
property of the literal restricted radical. The first construction then
applies. Neither construction needs finite-length preservation, an enumeration
of all simple roots, or a nonempty root system.

The provenance is an internal composition of the published
`RationalJacquetStages`, `RationalHaarModulus` and
`RationalInvolutivityReduction` interfaces. The quotient-stage comparison,
naturality and inverse maps are supplied by `RationalJacquetStages`; the Haar
identity and topological consequences are proved in the other two modules.
No new assertion from the original literature is introduced here. Normalized
induction in stages, exact-K0 term transitivity, induction compatibility and
the final rational involutivity statement remain separate proof obligations.
