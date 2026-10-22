# Full and prime-to-p scalars on integral Tate modules

This module equips the existing torsion-point inverse limits with continuous
scalar actions. It applies to a commutative group scheme `G` over a scheme `S`
and an arbitrary test scheme `T` over `S`. Specializing `G` to `A.toGrp` gives
the actions on the published Tate groups of an actual bundled abelian scheme.
The underlying groups, their discrete torsion levels, and their product-subspace
topologies are unchanged.

## Compatible residue actions

For a predicate `P` on natural numbers, the index type consists of positive
integers satisfying `P`. Suppose a commutative ring `R` has ring homomorphisms
`r n : R →+* ZMod n` compatible with reduction whenever one selected index
divides another. `ScalarAction.module` constructs a module structure on
`Integral G T P` by the formula

\[
(a x)_n=r_n(a)x_n.
\]

The residue-module structure on the actual torsion group is the published
`levelZModModule`. The proof that the formula preserves coherent families uses
`transition_zmod_smul`: multiplication by the quotient of two indices commutes
with the corresponding residue scalars. The module laws are verified at each
coordinate. The construction permits arbitrary `P`, including an empty index
set, and makes no cofinality or geometric finiteness assumption.

`ScalarAction.continuous_smul` proves joint continuity when all the residue
maps are continuous. Each coordinate factors through the product of the
discrete residue ring and the discrete torsion group. Product and subspace
continuity then give the result. `ScalarAction.map_smul` proves that the
published coordinatewise map induced by a group-scheme homomorphism preserves
the action. At each coordinate, a residue scalar is represented by an integer,
and the assertion follows from additivity.

## Full and away scalar rings

`fullReduction` evaluates the published `Global.ProfiniteIntegerRing` at each
selected positive index. Its compatibility gives `fullModule`, a module
instance on every `Integral G T P`. In particular this is the full
profinite-integer action on `Full G T`. `fullContinuousSMul` records joint
continuity, and `evaluation_full_smul` gives the coordinate formula.

For a natural number `p`, `awayReduction` evaluates
`Global.PrimeToProfiniteIntegerRing p` at the selected coprime index.
`awayModule` and `awayContinuousSMul` supply the continuous action on
`Away G T p`; `evaluation_away_smul` states its coordinate formula. No primality
assumption is needed for this construction. When `p` is prime, this is the
usual prime-to-`p` index convention.

`full_intCast_smul` and `away_intCast_smul` identify the action of an integer's
residue family with ordinary integer multiplication. `restrictAway_smul`
proves that restriction of a full Tate family is semilinear for the published
restriction homomorphism of scalar rings. `full_smul_eq_away_smul` identifies
the full-ring action on an away limit with the action through that same scalar
restriction. These last two identities follow directly from the coordinate
formulas; no comparison between distinct inverse-limit models is assumed.

`fullLinearMap` and `awayLinearMap` bundle the existing induced Tate maps as
linear maps over their respective scalar rings. Their underlying additive maps
are the published `map` maps, so their continuity, identity, composition and
additivity follow from those existing laws. The same names in
`Langlands.AbelianScheme.Tate` specialize these constructions to actual
abelian-scheme homomorphisms using `AbelianScheme.groupHom`. The module and
continuity instances also apply directly to the published abelian-scheme
`Integral`, `Full`, `Away`, `FullAt` and `AwayAt` abbreviations.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Chapter I, printed p.18 (PDF p.26), defines the full and away-from-primes
Tate limits used here. Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft, (10.2), printed p.142 (PDF p.146), gives the coordinatewise
compatible-residue action on the prime-adic Tate module. The present
arbitrary-predicate, arbitrary-test-scheme construction is an internal
generalization of that formula to the published full and coprime-modulus
residue rings. Its algebraic and continuity laws are proved in Lean as
described above, rather than attributed as general statements to those sources.

This module does not assert finite generation, freeness, rank, compactness of
the Tate group, a comparison with prime-adic products, a finite-adele scalar
action on the rational Tate group, or a geometric monodromy or pairing theorem.
Those require their separate constructions or hypotheses. In particular the
full scalar ring here is the published residue inverse limit; a comparison
with the separate group-theoretic profinite completion is not used.
