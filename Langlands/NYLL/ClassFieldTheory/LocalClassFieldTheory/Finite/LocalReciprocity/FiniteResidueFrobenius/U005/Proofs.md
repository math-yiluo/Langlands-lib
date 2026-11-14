# M167.005: `finiteResidueFrobeniusExponentHom_one` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentHom_oneStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentHom_one`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order). As in the source, the theorem is `@[simp]`.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 79–85. Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

Take M167.004 at `m = 1` as a hypothesis `h`, unfold its `abbrev` target `finiteResidueFrobeniusExponentHom_intCastStatement` in `h`, and close the goal with `simpa using h` (the casts `((1 : ℤ) : ZMod _) = 1` and `Frob ^ (1 : ℤ) = Frob`). The source proof is `simpa using finiteResidueFrobeniusExponentHom_intCast k L 1`; the explicit unfolding is added because `simpa using h` does not unfold the target in the type of `h`.

## Imports and modifications

Imports: the M167.004 proof module `...FiniteResidueFrobenius.U004.Proofs`. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
