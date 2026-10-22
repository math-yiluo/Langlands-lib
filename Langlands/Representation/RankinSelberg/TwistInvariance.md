# Determinant twists of JPSS zeta values

Worker 31 proves the determinant-twist interface for the zeta values and
L-polynomials of the published `LocalFactor` module. The integrals are those
of Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions*
(1983), §2.4, printed page 387, and the factors are those of Theorem 2.7,
printed pages 390–391. Both pages were read directly from the original scan.
The source is registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source does not state these twist identities as numbered results. They
are elementary consequences of the integral formulas, proved here.

## Determinants of the block matrices

`det_rankInclusion` proves that Worker 6's rank inclusion
`g ↦ diag(g, I_m)` preserves the determinant. The block sum is the reindexed
Mathlib `Matrix.fromBlocks g 0 0 1`, so Mathlib's `det_reindex_self` and
`det_fromBlocks_zero₂₁` apply. `det_appendIdentity` iterates this for the
published `appendIdentity` of `QuotientIntegrals`. `det_rectangularUnipotent`
proves that the published factor `1 + X` has determinant one: `X` is nonzero
only in rows below and columns inside the leading block, so `1 + X` is lower
triangular with unit diagonal (Mathlib's `det_of_isLowerTriangular`).
Hence `determinant_unequalRankMatrix`: the unequal-rank block matrix
`[g, 0, 0; x, I_j, 0; 0, 0, I_(k+1)]` has determinant `det g`.

## Whittaker sets of twisted representations

For a character `χ : Fˣ → ℂˣ`, `mem_whittakerSet_twist_iff` proves that the
Whittaker functions of `π ⊗ (χ ∘ det)` (the published `Langlands.twist` of
Worker 4) are exactly the functions `g ↦ χ(det g) W(g)` with `W` a Whittaker
function of `π`. `mem_inverseWhittakerSet_twist_iff` is the inverse-character
version. Both use the published `twistFunctional`, `untwistFunctional` and
`twistFunction_coefficient` of `Whittaker/AlgebraicTwist`. They also use the
triviality of `χ ∘ det` on unipotent matrices, `determinantCharacter_unipotent`
of `Whittaker/Twist`.

## Zeta values

`equalRankIntegrand_congr` and `unequalRankIntegrand_congr` show that the
published integrands agree whenever the products of the two Whittaker
functions agree at every point (at every block matrix in the unequal case).
`twist_product_cancel` cancels `χ(det g)` against `χ⁻¹(det g)`.

`equalRankZetaValues_twist` proves that the equal-rank zeta values of
`(π ⊗ (χ ∘ det), π' ⊗ (χ⁻¹ ∘ det))` equal those of `(π, π')`, for every
quotient measure, absolute value, `q` and `ψ`. The integrands, hence the
convergence predicates and the integrals, are literally equal.
`unequalRankZetaValues_twist` proves the same for every block family `(j, k)`
and rectangular measure, using `determinant_unequalRankMatrix`.
`isEqualRankLPolynomial_twist` and `isUnequalRankLPolynomial_twist` give
equality of the L-polynomial relations.

## Character pairs and standard factors

`twist_rankOneCharacter` proves that twisting the rank-one character `χη` by
`η⁻¹` gives `χ`, as representations on `ℂ`. `determinant_characterPairRank`
and `twist_comp_characterPairRank` show that determinant twists commute with
the identity relabelling `characterPairRank`. Together these give
`characterZetaValues_twist`: the zeta values of `(π ⊗ (η ∘ det)) × χ` are
those of `π × χη`, in rank one and in every higher rank.
`isCharacterLPolynomial_twist` is the corresponding L-polynomial statement.
With `χ = 1`, `isStandardLPolynomial_twist` says that the standard L-polynomial
of `π ⊗ (η ∘ det)` is that of `π × η`.

All statements concern the zeta-value sets and L-polynomial relations. They
assume neither convergence, nor rationality, nor existence of a generator.
Unramified twists `|det|^t`, which shift the spectral variable, are not
treated here.
