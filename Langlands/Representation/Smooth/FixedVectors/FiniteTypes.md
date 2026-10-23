# Compact open fixed vectors for a finite family of types

Proof of the accepted Library statement `FiniteTypeCompactOpenDetectionStatement`
(module `Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement`), the
finite-type step in the constituent argument. The proof was drafted by Worker 196
and is submitted unchanged in its Lean content. It isolates the elementary
compact-open choice and transport used with the finite family supplied by the
block-isolation interface discussed with Worker 166. It does not establish block
isolation or the constituent theorem.

The coefficient ring, group, two carriers and finite index type have independent
universes. No ambient finite-dimensionality is assumed. The choice requires a
smooth representation, a nonarchimedean group and weak local compactness. The
family can be empty. Its members need only be nonzero, rather than irreducible.

`fixedVectors_comp_subtype` identifies fixed vectors after group restriction,
provided the fixing subgroup is contained in the restricted subgroup. Its proof
constructs the actual nested subgroup elements in both directions.

`exists_compactOpen_fixing_finite` chooses an open stabilizer for each vector,
intersects their finitely many identity neighborhoods with the prescribed
neighborhood, and uses the published compact-open subgroup basis. Antitonicity
of fixed vectors preserves all chosen vectors.

`exists_compactOpen_fixed_finite_types` chooses a nonzero vector in every member
of the family of subrepresentations of the restriction to an open subgroup H.
It applies the preceding lemma with the additional neighborhood H, obtaining an
ambient compact-open K contained in H. Each vector is then fixed in its own
subrepresentation by the actual subgroup `K.comap H.subtype` of H.

`fixedVectors_meet_atoms_of_types` takes actual representation equivalences from
family members to the simple subrepresentations of a second restriction. It
maps their chosen vectors through those equivalences, proves nonzeroness by
injectivity, and uses `fixedVectors_comp_subtype` to recover ambient K-fixity.
This algebraic transport lemma requires no topology, smoothness, compactness,
semisimplicity or finiteness of the index type.

This is an internal derivation from the published smoothness, fixed-vector and
compact-open basis definitions and results, and Mathlib's subrepresentation and
representation-equivalence constructions. The planned application is the
fixed-vector choice in Bernstein–Zelevinsky (1976), Proposition 3.30, proof (3),
printed page 37. The finite-type family and its coverage are explicit hypotheses;
no assertion about their existence is made here.

`finiteTypeCompactOpenDetection` assembles the lemmas with exactly the full
proposition `FiniteTypeCompactOpenDetectionStatement`. The second representation
is quantified after K has been chosen, so K works uniformly for all covered
representations in the specified independent carrier universe. The statement
pair is the independently accepted Library statement, imported by its Lean name
and left unchanged; this proof is submitted against it.
