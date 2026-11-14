# M167.018: `restrictNormalHom_finiteResidueFrobeniusFromZHat` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_finiteResidueFrobeniusFromZHatStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_finiteResidueFrobeniusFromZHat`,
whose type is the target applied to the source parameters. It is stated under the source's
`variable` blocks, including the `Tower` block, so its binders are those of the target in the
same order.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`,
lines 272–289. Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

As in the source: unfold the target and rewrite both sides with M167.012
(`finiteResidueFrobeniusFromZHat_apply`). Rewrite the restricted side with M167.017
(`restrictNormalHom_finiteResidueFrobeniusExponentHom`). By `congr 2` and `Multiplicative.ext`,
the goal becomes the compatibility of the reductions of `z.toAdd : ZHat` modulo `[F:k]` and
`[E:k]`. This is the published M008.022 theorem
`Langlands.NYLL.ClassFormation.zHatReduction_transition` (whose type is its target
`zHatReduction_transitionStatement`), applied to `[E:k] ∣ [F:k]`, with witness `[F:E]` from
`Module.finrank_mul_finrank`, and the positivity of both finite degrees (`Module.finrank_pos`).

## Imports and modifications

Imports: the M167.012 and M167.017 proof modules, and the published M008.022 proof module
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U022.Proofs`. The
namespace is prefixed by `Langlands.NYLL`. The theorem's stated type is the `Statement` target
instead of the source proposition (definitionally the same). The proof route is the source's.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
