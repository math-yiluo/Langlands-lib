# Smooth test invariance for the intermediate lower-block comparison

Supporting work by Worker 318. This is a derived coefficient-level
step in the intermediate-rank calculation of JPSS section 9.3, printed
456–457. It does not prove the quotient disintegration or span inclusion.

The zero-and-identity diagonal of the actual lower chart equals the published
`rankInclusion`. The entry formula is reused from
`Langlands.RankinSelberg.rankInclusion_entry` in
[RankOneExtensionSpanTransfer](RankOneExtensionSpanTransfer.md).
Comparing these entries with `appendIdentity_entry` proves that
`rankInclusion` is the iterated JPSS identity extension after the explicit
`finCongr` rank cast. A version retains an independently specified source
rank. Consequently the full three-block chart is the identity extension of
the test-rank chart, and its diagonal restriction is the single identity
extension by the sum of the middle and final block sizes. These equalities
keep the actual matrices, both rank transports and the consecutive coordinate
order visible; no unspecified embedding is substituted.
A final adapter compares the diagonal chart directly with the extension
theorem's matrix at an independently specified full rank. Its proof
transports the established chart equality, then checks the entries after the
two rank casts.

The actual lower-block matrix factors as the displayed diagonal leading block
times a right perturbation whose leading block is the identity. That right
perturbation depends only on the rectangular and lower-triangular coordinates,
and equals the group identity at zero and identity. Its continuity is proved
in the matrix-unit topology by checking the actual matrix and its inverse.
The block multiplication proof keeps the lower-left entry equal to `x`;
it introduces no hidden multiplication by the leading block.

For a specified actual inverse Whittaker coefficient of a smooth
representation, `model_isSmooth` supplies an open subgroup fixing that
coefficient vector. Continuity pulls this subgroup back to a neighborhood of
zero and identity in the product of the two parameter spaces. The product
neighborhood property supplies separate neighborhoods. The factorization then
gives the same coefficient value for every leading invertible matrix and
every perturbation in those neighborhoods. The rank equality is implemented
by the entry-preserving `reindex (finCongr hn)` homomorphism.

The result uses arbitrary field and representation universes. It requires
smoothness and actual coefficient membership, without irreducibility,
Whittaker uniqueness, rational continuation or an integral comparison. The
target task later supplies smoothness from its retained Whittaker-type
hypothesis and applies the separate lower-block localization result inside
these neighborhoods.

For a supplied p-adic topological realization, a further lemma proves that the
normalized determinant-norm-one locus of the lower-triangular group is an
identity neighborhood. It pulls back the published open determinant kernel
along the actual subgroup inclusion and identifies membership by the real
value of the normalized absolute value. Intersecting this neighborhood with
the smooth-test neighborhood allows the later localization to keep every
lower-triangular determinant weight equal to one. No assertion about an
arbitrary compact subgroup is used.

Provenance is internal derivation from the published lower-block coordinate
construction and smooth coefficient model. The motivating original is the
registered source `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
