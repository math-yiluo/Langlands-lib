# Fixed-vector generation of irreducible representations

This is an internal consequence of the published definition of
`fixedVectorGenerated`, Mathlib's actual irreducibility predicate, and the
published compact-open fixed-vector exactness theorem. It introduces no new
structural assumption and has no external source claim.

`IrreducibleFixedVectorGenerationStatement` says that, for any topological
group, any subgroup and any irreducible smooth complex representation,
generation by the fixed vectors is equivalent to nontriviality of their
actual vector space. The group and representation-carrier universes are
independent. Neither openness nor compactness of the subgroup is required.

The proof `irreducibleFixedVectorGeneration` uses the bottom/top dichotomy
for invariant submodules. If the fixed space were zero, the bottom
subrepresentation would contain it and generation would force bottom to
be top, contradicting irreducibility. Conversely, a nonzero fixed vector
rules out bottom for every subrepresentation containing all fixed vectors;
irreducibility then makes that subrepresentation top.

`SmoothRep.nontrivial_fixedVectors_of_isSubquotient` applies to an actual
smooth subquotient at a compact open subgroup. Choose a nonzero fixed
vector and apply the already published
`SmoothRep.exists_nonzero_fixedVector_of_isSubquotient`. That theorem lifts
the vector through the quotient using compact-open exactness, then maps it
through the injective subrepresentation witness. The resulting ambient
fixed vector is nonzero. This wrapper asserts nontriviality of fixed
spaces, rather than nontriviality only of the underlying representation.
