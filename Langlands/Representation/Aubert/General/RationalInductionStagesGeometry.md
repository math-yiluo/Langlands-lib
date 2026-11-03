# Actual subgroup identities for rational induction in stages

This internal deduction supplies group identities for the actual rational
standard subgroups, using the target's existing
`StandardLeviIntersectionStatement` and `StandardCocharacterStatement`.
It does not assert normalized transitivity or the Aubert induction equation.
The definitions and structural premises are imported from the published Library;
no additional structural or representation theorem is assumed.

For finite root subsets `I ⊆ J`, `unipotent_product_of_subset` specializes
the radical product in the intersection statement to these exact labels.
The all-test Levi inclusion in the same statement gives
`levi_le_of_subset`. The product formula, applied with the first factor equal
to one, gives the reverse radical inclusion `U_J ≤ U_I`. Every element of
`U_I` is a product of an element of `M_J ∩ U_I` and one of `U_J`, so it lies
in `P_J`. The existing actual decomposition `P_I = M_I U_I`, derived from
the standard-cocharacter statement, then proves `P_I ≤ P_J`.

The generic group lemmas use only an actual semidirect decomposition.
If `U ≤ Q ≤ P`, the projection of `q ∈ Q` lies in `Q`, since its complementary
radical factor also lies in `Q`. This proves that `Q.subgroupOf P` is the
inverse image of `Q.subgroupOf M` under the projection. Restriction along the
actual Levi inclusion gives `Q.subgroupOf M` by definition.
For nested decompositions, the two successive radical factors multiply to an
element of the finer radical; uniqueness of the finer Levi projection proves
`projection_stages`. The homomorphism `stageProjection` constructs this
composite: include the fine parabolic into the coarse one, project to the
coarse Levi, restrict the codomain to the fine parabolic's intersection with
that Levi, project inside the Levi, and flatten the nested subgroup.
`stageProjection_eq` identifies it with the finer projection as a monoid
homomorphism. These generic constructions quantify over any group in
universe `u`; they assume no topology.

The rational adapters give the exact inverse-image identity and kernel
inclusion for `P_I` inside `P_J`. `standardLeviProjection_stages` specializes
projection composition to the target's literal labels `I : Finset J`,
`leviIndex J I`, and the existing restricted standard-Levi decomposition.
Its source and target are the published ambient and restricted projections.
No independently chosen Levi family or reindexing of root signs is used.
The proofs apply to every subset, including empty and full subsets, without a
nonemptiness assumption. They use no topology, finite length, geometric lemma,
classification, character independence, adjointness or cuspidal-support theorem.

This pair is an internal derivation from
`RationalLeviDecomposition`, `RationalParabolicDecomposition`, and the
semidirect-projection identities in `Parabolic`. The needed Haar-modulus
factorization and comparison of normalized smooth induction remain subsequent
proof obligations.
