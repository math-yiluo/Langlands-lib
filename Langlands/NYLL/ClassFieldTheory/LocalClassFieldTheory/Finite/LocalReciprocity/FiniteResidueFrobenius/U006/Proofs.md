# M167.006: `finiteResidueFrobeniusExponentHom_surjective` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentHom_surjectiveStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentHom_surjective`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order).

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 87–97. Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

Given `σ`, Mathlib's `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow` gives `m : Fin [L:k]` with `Frob ^ m = σ`. The preimage is `ofAdd ((m : ℤ) : ZMod [L:k])`: rewrite with M167.004 and conclude with `simpa [zpow_natCast]`. This is the source proof.

## Imports and modifications

Imports: the M167.004 proof module. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
