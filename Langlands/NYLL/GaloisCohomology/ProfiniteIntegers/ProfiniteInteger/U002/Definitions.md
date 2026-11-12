# NYLL M009.002: natural multiplication on the profinite integers

The declaration `Langlands.NYLL.ClassFormation.zHatMulNat` adapts
`ClassFormation.zHatMulNat` from
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`, lines 51–56
(definition at line 52), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The original file SHA-256 is
`b2fcb523b7bf0408b776c71df6d528d446d7d373634df6e5df43183d57fc5ae6`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The explicit parameter is `n : ℕ`, with no positivity hypothesis. The result is
`ContinuousAddMonoidHom ZHat ZHat`, acting by `x ↦ n • x`. Here `ZHat : Type 0`
is the published NYLL closure of the diagonal integers in the product of all
positive `ZMod` quotients. Its additive group and topology are the canonical
structures imported from `ProfiniteIntegerCore.Definitions`. Thus this is an
actual bundled continuous additive map on the source model. It includes the
zero map when `n = 0` and introduces no ambient group or universe parameter.

Worker 120 retains the original copyright and author header, docstring, name
suffix, noncomputable section and all four construction fields. The namespace
is prefixed with `Langlands.NYLL`. The original imports of Mathlib cardinal
finiteness, neighborhoods, subgroup kernels and indices, and of the whole
NYLL `ProfiniteIntegerCore`, are replaced by the published focused core data
module. Only the original `ZHat` instances and Mathlib's scalar multiplication
and `continuous_nsmul` are used in this body. No preceding M009.001 exponent
injectivity result or later M008 theorem is used; focused compilation checks
this smaller import boundary.

This unit supplies the data map only. It proves no named evaluation,
injectivity, closed-range, kernel, index or finite-index subgroup-classification
statement, and supplies neither the range equivalence nor division map. Those
remain separate source units. It introduces no instances and asserts no
comparison to another profinite-integer model or reciprocity result.

The original Apache-2.0 attribution is retained. See `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
