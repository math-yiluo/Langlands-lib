# Openness and Haar conullity of the regular loci

`sigmaRegularOpenConull` proves `SigmaRegularOpenConullStatement` for every
nonarchimedean local field, cyclic algebra, and rank.
`regularSemisimpleOpenConull` proves `RegularSemisimpleOpenConullStatement` by
specializing the σ-regular result to the base field with the identity
automorphism and degree one.

`sigmaRegularOpen_of_cyclicNormLemma` gives openness from `cyclicNormLemma`.
For conullity, a finite basis of the matrix algebra gives a continuous
linear equivalence with a finite product of copies of the base field. The
local field has a nonisolated zero, so its additive Haar measure vanishes on
singletons. `ae_eval_ne_zero` gives nullity of the zero set of the coordinate
polynomial for the product of these measures. The continuous linear
equivalence transports the product measure to additive Haar measure on the
matrix algebra and the zero set to a closed null set there.
`finiteAlgebra_isOpenEmbedding_unitsVal` gives the open unit locus, and
`measure_preimage_unitsVal_eq_zero` gives nullity of the preimage for every
Borel Haar measure on the units. This preimage is the complement of the
σ-regular locus by `exists_sigmaRegular_polynomial`.

For the degree-one specialization \(E=F\), the cyclic norm and scalar
extension act as the identity. Association is ordinary conjugacy, and the
proof applies `isRegularSemisimple_conj_iff`.

The proofs use separability of the characteristic polynomial in all
characteristics. The regular-set integrations are motivated by
Henniart–Lemaire (2011), I.5.1 and II.1.3, with cyclic algebras treated in
II.2.8. The ordinary locus appears in Harish-Chandra (1999), Introduction.
[Statement and source locations](RegularSetOpenConullStatement.md)
