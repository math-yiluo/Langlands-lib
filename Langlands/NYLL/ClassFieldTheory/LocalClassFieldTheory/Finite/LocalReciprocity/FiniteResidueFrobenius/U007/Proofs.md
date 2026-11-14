# M167.007: `finiteResidueFrobeniusExponentHom_injective` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentHom_injectiveStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentHom_injective`, whose type is the target applied to the
source parameters, under the source's `variable` blocks (so its binders are those of the target
in the same order).

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`, lines 99–109. Registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

Both sides have cardinality `[L:k]`: `Nat.card (Multiplicative (ZMod [L:k])) = [L:k]` by `Nat.card_zmod` (with a local `NeZero` from `Module.finrank_pos`) and `Nat.card Gal(L/k) = [L:k]` by `IsGalois.card_aut_eq_finrank`. A surjection (M167.006) between finite types with `card` of the source at most that of the target is bijective (`Function.Surjective.bijective_of_nat_card_le`); take its injectivity. This is the source proof.

## Imports and modifications

Imports: `Mathlib.SetTheory.Cardinal.Finite` (as in the source imports) and the M167.006 proof module. The namespace is prefixed by `Langlands.NYLL`; the theorem's stated type is the
`Statement` target instead of the source proposition (definitionally the same).

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
