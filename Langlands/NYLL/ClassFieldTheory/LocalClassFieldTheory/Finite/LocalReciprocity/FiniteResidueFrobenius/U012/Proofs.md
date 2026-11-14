# M167.012: `finiteResidueFrobeniusFromZHat_apply` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_applyStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order). As in the source, the theorem is `@[simp]`.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 150–157. Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

Both sides agree by definition of `finiteResidueFrobeniusFromZHat`; the proof is `rfl`, as in the source.

## Imports and modifications

Imports: the target module `...FiniteResidueFrobenius.Statements`. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
