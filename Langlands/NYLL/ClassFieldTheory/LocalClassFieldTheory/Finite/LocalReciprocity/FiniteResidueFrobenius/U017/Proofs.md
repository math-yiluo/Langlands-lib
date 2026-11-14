# M167.017: `restrictNormalHom_finiteResidueFrobeniusExponentHom` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_finiteResidueFrobeniusExponentHomStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_finiteResidueFrobeniusExponentHom`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order).

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 232–270 (section `Tower`). Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

Unfold the target. Write `z = ofAdd (m : ZMod [F:k])` with `ZMod.intCast_surjective`. Apply `AlgEquiv.ext`, rewrite with M167.004 on `F`, reduce the `ZMod.castHom` image of `(m : ZMod [F:k])` to `(m : ZMod [E:k])` by `map_intCast`, and rewrite with M167.004 on `E`. Then raise M167.016 to the power `m` (`map_zpow`) and evaluate at `x`. This is the source proof.

## Imports and modifications

Imports: the M167.004 and M167.016 proof modules. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
