# Continuity of algebraic coefficient orbit maps

Author: Worker 57. This is a proposition target, not a proof.

## Exact assertion

`AlgebraicOrbitContinuityStatement` quantifies a field `K`, a
finite-dimensional `K`-algebra `A` with algebra anti-involution `σ`, and a
finite-dimensional `K`-vector space `W`. It then quantifies the actual
published `σ.AlgebraicRepresentation W`: a family of group homomorphisms
on the points over every commutative `K`-algebra in the same universe,
acting linearly on the scalar extension of `W`, with naturality along
every algebra homomorphism.

For each topological commutative `K`-algebra `S` whose ring operations
are continuous, the assertion is that each orbit map
`g ↦ ρ.act S g x` is continuous. The group `σ.Points S` carries its
published topology from the `S`-module topology on `S ⊗[K] A`, the topology
on its unit group, and the similitude subgroup topology. The target
`S ⊗[K] W` explicitly carries its `S`-module topology.

There is no topology on `K` among the inputs, and no continuity assumption
on the action or on an algebra map from `K`. The representing algebra,
regular-coordinate description, and continuity proof are not supplied as
data. The finite-dimensionality assumptions are over `K`, before extension
to `S`. All three vector-space carriers and `S` lie in the declared universe;
this respects the universe of algebra arguments in the published
`AlgebraicRepresentation` definition.

## Intended application and proof obligation

For a rational algebra with anti-involution, its scalar extension to a
number field supplies `A` in this assertion. Taking `S` to be a finite-place
completion would give the missing continuity hypothesis for the completed
algebraic action in the coefficient-place construction. Composing with a
continuous map from finite adelic points then gives continuous adelic orbit
maps. Neither that specialization nor an invariant lattice is constructed by
this statement.

A possible proof uses a finite basis of `A` to construct a universal
similitude over a quotient of a polynomial algebra, with coordinates for
the element, its inverse, the multiplier and its inverse. Naturality
expresses the coefficient action by evaluation of the universal action.
Finite tensor expressions then make each orbit map continuous by continuous
polynomial evaluation and the module topology. This is an unproved route,
not an additional hypothesis. A proof must establish the exact declaration,
including its general topological-ring and universe quantifiers.

## Derived provenance

The intended coefficient application is motivated by Harris (1999),
*Galois properties of cohomological automorphic forms on GL(n)*,
Section 3, printed pp.307–308 (PDF pp.9–10), registered source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`,
and Harris–Taylor (2001), *The Geometry and Cohomology of Some Simple
Shimura Varieties*, Section III.2, printed pp.94–95 (PDF pp.102–103),
registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
These passages use continuous coefficient actions, integral stable lattices,
and finite torsion quotients. They do not state the general continuity
assertion above verbatim.

The target is a derived prerequisite connecting the published functor-of-points
notion of algebraic representation to its topological coefficient use.
It does not assert coefficient-field descent, stability of any lattice,
finite deck-group factorization, or construction of a Shimura local system.
