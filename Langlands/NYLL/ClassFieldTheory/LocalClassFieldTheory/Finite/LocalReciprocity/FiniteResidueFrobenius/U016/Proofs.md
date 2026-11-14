# M167.016: `restrictNormalHom_finiteResidueFrobenius` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_finiteResidueFrobeniusStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_finiteResidueFrobenius`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order). The theorem is stated under the source `Tower` `variable` block, so the unused hypothesis `[Finite E]` is a binder, as in the target.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 203–230 (section `Tower`, variables 205–208). Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

Apply `AlgEquiv.ext` and the injectivity of `algebraMap E F`. Then `AlgEquiv.restrictNormal_commutes` identifies the image of the restricted Frobenius with Frobenius of `F` applied to `algebraMap E F x`, which is `(algebraMap E F x) ^ #k = algebraMap E F (x ^ #k)` by `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` and `map_pow`. This is the source proof.

## Imports and modifications

Imports: the target module `...FiniteResidueFrobenius.Statements`. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
