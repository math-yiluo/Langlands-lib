# Quotient actions on actual normal-level spaces

This internal construction extends the published `Langlands.Shimura.Levels`.
It uses the actual double-quotient relation, right-translation maps and quotient
topology from that module, and Mathlib's quotient-group factorization. Its
provenance is this categorical and quotient construction; no new external
source claim is made.

The inputs are groups `Γ` and `G`, a homomorphism `ι : Γ →* G`, a `Γ`-space `X`,
a subgroup `U` of `G` and a normal subgroup `N` of `U`. The three carriers have
independent universes. The spaces `X` and `G` have topologies, and `G` is a
topological group. Continuity of the `Γ` action is not a hypothesis.

`sublevelSubgroup U N` is the image of `N` in `G` under `U.subtype`. It is
contained in `U`, and inclusions of relative subgroups give inclusions of these
ambient subgroups. Relative normality does not assert normality in all of `G`.

`normalLevelAction` acts on the actual space
`Γ \ (X × G) / sublevelSubgroup U N`. An element `u` of `U` sends `[x,a]` to
`[x,a u⁻¹]`. The inverse is essential: it makes the right-translation maps a
left action with Mathlib's multiplication on categorical endomorphisms.
Normality supplies the conjugation condition needed for well-definedness;
the quotient topology gives continuity of each map. Identity and multiplication
laws are proved on quotient representatives using the group laws.

`normalLevelAction_kernel` proves that `N` acts trivially. The proof checks
representatives with the actual double-quotient equality criterion, using a
right factor in `N`. `normalQuotientAction` then factors this monoid homomorphism
through `U / N`. Its value on a quotient representative is the original
inverse right translation.

For an inclusion `N ≤ P` of normal subgroups of the fixed `U`,
`normalQuotientMap` is the actual homomorphism `U / N → U / P` induced by the
identity on `U`. `normalCoverMap` is the continuous map that forgets the finer
level. Its quotient equivariance is proved by induction on the group quotient
and on the space quotient; on representatives both sides multiply by the same
inverse element. The map is surjective. The quotient maps and the underlying
space maps satisfy the stated identity and composition laws.

`normalCoverProjection` is the continuous surjection from the finer quotient
to `Γ \ (X × G) / U`. On representatives it forgets the finer level.
`normalCoverProjection_invariant` proves that every element of `U / N`
preserves this projection: multiplication by `u⁻¹` is absorbed by the
right `U`-relation. `normalCoverMap_projection` proves compatibility of
forgetful maps with these projections. The identity, multiplication,
equivariance and composition proofs reduce to representatives; identity
and associativity in `G` then give the asserted equalities.

These are actions by continuous self-maps and actual equivariant level maps.
No joint continuity in the acting group, finiteness, freeness, topological
covering property, étale scheme realization, torsor structure, canonical model,
cohomology or Harris specialization is claimed. The subgroup `N` need not be
open, and `U` need not be compact. Stabilizers of the original rational action
can obstruct freeness.
