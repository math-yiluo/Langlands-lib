# Proof of full-center detection of a central generalized eigenvalue

Authors: Worker 19 and Worker 828 (the reused finite fixed-vector argument).

`Langlands.centralEigenvalueDetection` proves the complete unapplied
`Langlands.CentralEigenvalueDetectionStatement.{uG,uV}`. The auxiliary
`exists_centralExponent_of_generalized_eigenvector` supplies the same
result with the quantified data as arguments.

Choose an open subgroup `K` fixing the given nonzero vector `v`. Intersect
the generalized `μ`-eigenspace of `ρ z` with the `K`-fixed vectors to form
`W`. This space contains `v`, and admissibility makes it finite-dimensional.
Every central operator preserves both factors: it commutes with `ρ z` and
with every `ρ g` for `g` in `K`.

The restricted central operators commute. The published
`Langlands.EndomorphismBound.exists_common_eigenvector` gives a nonzero
common eigenvector `w` in `W`, and
`Langlands.EndomorphismBound.exists_character_of_forall_eigen` combines its
eigenvalues into a character `χ` of the full center. Since `w` is
`K`-fixed, `χ` is trivial on the inverse image of `K` in the center. That
inverse image is an open subgroup, so `χ` has open kernel.

The vector `w` belongs to `generalizedCentralCharacterSpace ρ χ` with
uniform exponent one. It is nonzero, so `χ` satisfies `IsCentralExponent`.
Finally, `w` is a `χ z` eigenvector lying in the generalized
`μ`-eigenspace. The published
`Langlands.eq_of_eigen_of_mem_genEigenspace` identifies these scalars.

This is an internal adaptation of the proof of
`Langlands.exists_eigencharacter_extension`, by Worker 828, which uses an
entire restricted generalized-character space in place of a single
operator's generalized eigenspace. It uses the published
`Module.End.mapsTo_genEigenspace_of_comp` for stability. It has no
representation-theoretic dependencies on Jacquet functors, classification,
the geometric lemma, adjointness, character independence, or cuspidal
support. It does not prove any coefficient bound or square-integrability
statement.
