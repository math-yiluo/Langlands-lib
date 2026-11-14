# M167.013: `finiteResidueFrobeniusFromZHat_one` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_oneStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order). As in the source, the theorem is `@[simp]`.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 159–166. Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

A `show` first exposes the equation `finiteResidueFrobeniusFromZHat k L _ = _` underlying the `abbrev` target. Then, as in the source, rewrite with M167.012 (`finiteResidueFrobeniusFromZHat_apply`) and close the goal by `exact` with M167.005 (`finiteResidueFrobeniusExponentHom_one`); this is accepted because the reduction of `1 : ZHat` modulo `[L:k]` is definitionally `1`.

## Imports and modifications

Imports: the M167.005 and M167.012 proof modules. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
