# Actual semistandard orbit packets from whole-domain continuations

`OrbitPacketData.conditionalOfFullDomainContinuation` constructs the scalar
data for a semistandard orbit packet at a specified compact open subgroup.
Its inputs are the actual dynamic parabolic products at that subgroup, a
`LeviNormalization` for the irreducible inducing representation, and
`ActualOppositeFullDomainContinuationStatement`. The last premise provides
continuations of both original standard integrals agreeing with those
integrals throughout their respective convergence domains. The two domains
each contain a nonempty open subset.

The construction uses the parabolic product at the given cocharacter and
its inverse to form the two compact pictures.
`DynamicInducedOrbit.DensityPackage.ofSquareIntegrable` then supplies an
open locus of irreducible inductions and regularity of the inverse of the
exact opposite composition scalar on the entire unitary parameter group.
`conditionalOfFullDomainContinuation_compact` identifies the stored compact
with the one used for the two original integrals.

This assembles the standard integrals from Waldspurger IV.1.1 and the
opposite scalar of IV.3, whose inverse enters the density of V.2.1 and the
wave packet of VI.3. The Lean construction works directly with the supplied
continuations and their open subregions.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, 2003, printed pp. 278, 285–287, 292–293 and
301–302. [DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
