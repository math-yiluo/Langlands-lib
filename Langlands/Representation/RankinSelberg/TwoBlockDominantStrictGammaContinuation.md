# Continuation of the strict-rank gamma product to zero

This internal unit proves the complete symmetric gamma product for the actual
lower two-block induction at the original parameter, when `t < r`. The test
representation has actual rank `r + 1`; the induced representation has actual
rank `t + 1`. The independent field, test and dependent block universes,
full Whittaker-type hypotheses, supplied character and supplied self-dual Haar
measure are preserved.

## The actual sign and dual transformation

`strictIntegral_central_translate` proves that translating an inverse-model
coefficient by the fixed central matrix `(-1)^r` scales the actual strict
integral by `zeta^r`. Here `r` is the larger index, exactly the exponent in
`UnequalRankGammaEquation`. The proof commutes the central matrix past the
evaluation point, applies `HasModelMinusOneScalar.pow_apply`, rewrites the
integral as its actual outer integral and extracts the constant scalar. It
works with total Bochner integrals, without adding convergence assumptions.

`StrictOppositeRealRayGammaCertificates` retains the complete symmetric gamma
certificate for the fixed opposite spectral product at every real parameter
above one bound. `exists_strictOppositeRealRayGammaCertificates` obtains the
large-twist certified product from `exists_strictTwoBlockSymmetricGammaProduct`,
discharging that theorem's first-block analytic premise with the published
`twoBlockDominantFirstBlockLaurentIdentity`. Complete unramified gamma transport
and factor uniqueness identify its block witnesses with the two fixed original
gamma factors, rescaled in opposite directions.

## Continuation of actual coefficient equations

`strictTwoBlock_gamma_at_zero` fixes arbitrary complementary rows `j,k` with
`r = t + (j + k + 1)`, a compatible quotient measure finite on compact sets,
nonzero fixed functionals and arbitrary coefficient tests. It extends the
original lower-induced coefficient to an actual opposite-twist family with
one common compact open right level, entire point values and its prescribed
value at zero.

The primal coefficient family uses its fixed central translate by `(-1)^r`.
The dual family swaps `j,k` and uses the fixed actual first-dual model
coefficient translated on the right by `blockWeylAt t r htr`, together with
the second dual of the varying inverse family. The first dual, including this
right Weyl translation, is realized by `translatedFirstDualModelEquiv` in the
same inverse-transpose representation. Thus the dual integral is exactly
`dualUnequalRankModelIntegralAt`, with its prescribed row swap and Weyl matrix.

The published common-level transformations for fixed translates and second
duals, followed by `strictSlices_entire`, prove entire dependence of both
literal coefficient families. At every complex parameter,
`strictRankCoefficient_continuationData` supplies rational continuations and
absolute bilateral spectral expansions for the same actual primal and dual
integrals. The full first-dual and second-dual type and nonzero-functional
lemmas supply the hypotheses; no varying scalar is divided out.

On the real ray, the complete gamma certificate specializes at the supplied
quotient measure and functionals, then at the fixed complementary rows and
tests. Its actual model scalar is absorbed into the primal rational
continuation using `strictIntegral_central_translate`. Uniqueness of rational
continuations identifies this equation with the independently constructed
primal and dual continuations. The sign-absorbed gamma equation consequently
has scalar one throughout the real parameter ray.

`StrictOppositeRealRayClearing` from the strict L continuation module supplies
finite Laurent clearing of the translated primal coefficients on that ray,
with the fixed original block L polynomials under opposite spectral
substitutions. `gammaFE_oppositeSpectralProduct_at_zero` combines those clearing
identities, the two entire coefficient families and their absolute spectral
expansions to continue the actual gamma equation to zero. The central-translate
identity at zero restores the original fixed model scalar, with exponent `r`.
The resulting continuations concern the original actual integral and its
literal transformed dual integral.

## Identification of the complete certified factor

`strictTwoBlockSymmetricGammaProduct_at_zero` derives full Whittaker type of
the actual lower induction from that of the blocks. Published symmetric gamma
and L existence provide certified factors for both original blocks and the
induced pair. No factor-existence hypothesis is added.

The proof takes the maximum of the real-ray L-clearing and gamma bounds. The
complete induced gamma certificate supplies a nonzero rational integral at
`j = 0`, `k = r - t - 1`, together with its functional equation. The preceding
continuation theorem gives the equation for the product of the fixed original
block factors on precisely the same tests. Rational-continuation uniqueness
identifies the primal and dual continuations, and the retained nonzero primal
integral allows `GammaFunctionalEquation.gamma_unique` to identify the already
certified induced gamma factor with that product. The complete symmetric
certificates for both blocks and their product are returned unchanged.

## Provenance and scope

This is an internal deduction from the separately reviewed strict real-ray
comparison, the published exact first-block theorem, actual opposite Whittaker
families, common-level transformations, full analytic expansion, unramified
transport and coefficientwise continuation machinery. It introduces no new
literature translation. It uses neither unrestricted multiplicativity nor
later rank descent. This unit proves the strict actual lower conclusion;
the exact target module combines the equal-rank boundary and actual normalized
lower-to-upper reversal.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictGammaContinuation` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
