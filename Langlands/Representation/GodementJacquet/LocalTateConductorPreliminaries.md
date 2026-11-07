# Natural rank-one conductors and scalar Fourier witnesses

Worker 1691 derives two preliminary clauses of the scalar Tate target over an
arbitrary nonarchimedean local field. These are internal consequences of existing
published proofs, with no new original-source assertion or analytic premise.

`exists_character_level` composes the continuous multiplicative character with
the rank-one determinant. The inverse image of the complex ball of radius one
half about one is a neighborhood of the identity. The published
`Conductor.rankOne_level_cofinal` supplies an actual level subgroup inside it.
Every nonnegative power of each element remains in that subgroup, so the
published `complex_eq_one_of_forall_norm_pow_sub_one_lt` forces its character
value to equal one. This argument uses neither characteristic zero nor an
assumed conductor.

`existsUnique_character_conductor` takes the least such natural level. Minimality
gives a nontrivial character value at every smaller level. Comparing the two
minimality characterizations proves uniqueness. The defined natural number
`characterConductor` selects that proved unique exponent;
`characterConductor_spec` exposes both exact level conditions.
`character_conductor_inv_iff`
records that inversion preserves the complete characterization.

`exists_scalar_fourier_witness` applies the published arbitrary-field
`HarmonicAnalysis.scalarFourierClosure` to the supplied self-dual measure and
adjoins `fourierIntegrand_integrable`. Its witness is a Schwartz--Bruhat function
whose values are exactly the actual plus-sign Fourier integral. It assumes no
Mellin continuation or functional equation.

The proof dependencies and their mathematical provenance are explained in the
unchanged `Conductor/RankOne.md`, `Twist/ContinuousCharacterProof.md` and
`HarmonicAnalysis/ScalarFourierClosureProof.md`. These preliminaries do not yet
prove the scalar Mellin analytic data, explicit Laurent generators, or the
exact-exponent functional equation of `LocalTateConductorStatement`.
