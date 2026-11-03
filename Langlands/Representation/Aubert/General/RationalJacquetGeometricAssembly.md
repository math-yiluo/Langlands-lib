# Rational Jacquet compatibility from the rational geometric expansion

Worker 165. This internal assembly proves
`RationalGeometricK0ExpansionStatement.{u,v} →
RationalJacquetCompatibilityStatement.{u,v}` with independent universes.
`RationalJacquetGeometricAssemblyStatement` names this implication. The actual
representation-theoretic geometric expansion is its sole additional premise.
The unconditional Jacquet target remains unproved here.

`rationalIntersectionExpansions_of_rationalGeometricK0Expansion` introduces
exactly the parameters of `RationalIntersectionExpansionStatement`. It derives
the ambient and literal inside-Levi `ParabolicFiniteLength` packages through
`standardParabolicFiniteLength` and
`standardLeviParabolicFiniteLength`, using the displayed topological,
compact-subgroup-limit and finite-length-preservation inputs.

For the original supplied point Coxeter system, it obtains
`actualLeviWeylIdentification` from
`actualLeviWeylIdentification_of_rootLength`. This uses connected reductivity,
the actual maximal split torus, the relative-root-system witness, the generic
cocharacter, the point normalizer and full-centralizer comparisons, and the
supplied literal root-sign length law. No canonical replacement of the supplied
system, extra Levi identification premise, or change of root labels is made.

`rationalPointGeometricExpansion_of_rationalGeometricK0Expansion` then
specializes the universal expansion with this derived identification. Its
actual intersection decompositions and factor-preservation witnesses are those
derived in `RationalJacquetGeometricExpansion` from
`pointSourceIntersectionIdentities`,
`geometricIntersectionDecompositions_of_pointSource`, and
`geometricTermFiniteLength_of_pointSource`. The next bridge,
`rationalIntersectionExpansion_of_pointGeometricExpansion`, identifies each
geometric term with the literal restricted-intersection term. This supplies
every row, for every standard subset and every normalizer-quotient section.

`rationalJacquetCompatibility_of_rationalGeometricK0Expansion` composes that
result with `rationalJacquetCompatibility_of_intersectionExpansions`. The
latter composes the rows with ambient Jacquet restriction, identifies the
common terms, applies weighted cancellation and the cardinality-preserving
associated-subset reindexing, and identifies the longest surviving term.
Consequently the conclusion retains exactly `longestRep cs J`,
`associatedSubset cs J`, all actual normalizer lifts, the actual normalized
finite-length K0 maps, and the unadjusted signs of the published target.

The field scope is every nonarchimedean local field, including positive
characteristic, and every connected reductive group scheme with the actual
maximal split torus. The topology is `pointTopology`; representation carriers
have universe `max (u + 1) v`. All displayed structural statements, ambient
and restricted preservation premises, and Coxeter comparison premises of the
Jacquet target are retained. Empty simple-root sets and empty and full subsets
remain covered.

The provenance is internal composition of the two imported published modules
and their declaration-level dependencies described above. This assembly uses
the geometric lemma only through the explicit, still unproved
`RationalGeometricK0ExpansionStatement` premise. It introduces no Langlands
classification, character-independence, adjointness or cuspidal-support
premise. No external literature assertion is made. Proving that geometric
expansion, and hence obtaining an unconditional proof of the host task's
target, remains a separate obligation.
