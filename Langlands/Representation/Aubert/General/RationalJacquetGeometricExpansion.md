# Literal rational intersection expansion from actual geometric terms

Worker 165. This internal bridge converts the actual geometric-lemma expansion
to the literal intersection rows used by rational Jacquet cancellation.
It retains the supplied point Coxeter system and literal simple-root labels.
The representation-theoretic geometric expansion remains an explicit premise.

`rationalIntersectionExpansion_of_pointSource_geometricExpansion` accepts the
three actual point-source intersection identities, arbitrary actual geometric
decomposition witnesses, their factor-preservation witnesses, and the actual
`GeometricK0ExpansionStatement`. At each source and target index and every
normalizer-quotient section it applies that equation. For each minimum
representative, `geometricTermK0_eq_intersection_of_pointSource` identifies the
actual geometric term with `rationalIntersectionJacquetTerm`. Equality of the
finite sums gives exactly `rationalIntersectionExpansion`. There is no composition
with ambient source Jacquet restriction at this step.

`rationalPointGeometricExpansion` is a proposition naming the same actual
geometric equation with its structural prerequisites derived. The proved
`pointSourceIntersectionIdentities` supplies source geometry from the retained
point root-length and simple-reflection comparisons and the standard-cocharacter
and standard-Levi-intersection statements. Inverting the minimum representative
gives target geometry. The standard semidirect decompositions inside the literal
Levis then give both actual geometric decompositions. The restricted
`ParabolicFiniteLength` packages give finite-length and short-exact preservation
of the actual source Jacquet and target induction factors through
`geometricTermFiniteLength_of_pointSource`.

`rationalIntersectionExpansion_of_pointGeometricExpansion` applies the first
bridge to these derived witnesses. Neither this bridge nor the pointwise
expansion predicate uses `actualLeviWeylIdentification`.

`rationalPointGeometricExpansion_of_rationalGeometricK0Expansion` specializes
the separate universal rational geometric target to precisely these derived
witnesses. It uses the canonical simple-root enumeration supplied by the
relative-root system, derives ambient preservation by
`standardParabolicFiniteLength`, and retains that universal target's explicit
`actualLeviWeylIdentification` premise. This identification remains unproved
here and is not added to the final Jacquet target.

The field and representation universes are independent, with representation
carriers in `max (u + 1) v`. The topology is the actual rational-point topology.
Local compactness, the nonarchimedean-group property, closed radicals and
closed Levis, actual ambient and restricted preservation packages,
standard-cocharacter and Levi-intersection statements, and the actual point
normalizer, centralizer and root comparisons remain explicit. The term
comparison also retains standard Levi conjugation. The final specialization
additionally uses the local-field and Hausdorff hypotheses and the ambient
topological and finite-length inputs of the universal target. Every minimum
representative and every chosen normalizer lift is covered, including empty
simple-root sets.

The provenance is internal composition of the existing actual geometric-term
comparison, Worker 1186's point-source geometry, and the literal row predicate
in `RationalJacquetCancellation`. No new assertion from literature is made.
Neither the geometric expansion nor the unconditional
`RationalJacquetCompatibilityStatement` is proved here.
