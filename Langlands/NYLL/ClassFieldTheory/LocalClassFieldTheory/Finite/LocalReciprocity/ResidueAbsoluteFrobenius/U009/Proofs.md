# M168.009: `residueAbsoluteFrobenius_one` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_oneStatement` as
`@[simp] theorem Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_one`, whose type
is the target applied to the source parameters, under the source's `variable` block (so its
binders are those of the target in the same order). The target is an `abbrev`, so the theorem is
a usable simp lemma, as the source `@[simp]` theorem is.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`,
lines 161–177. Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

The source proof. By injectivity of `InfiniteGalois.continuousMulEquivToLimit k Omega`,
`Subtype.ext` and `funext`, it suffices to show that both sides have the same restriction to
every finite Galois intermediate field `E` (the coordinate at `E`, made explicit with `change`).
The restriction of `residueAbsoluteFrobenius k Omega (ofAdd 1)` is `Frob_E` by the M168.007
theorem, and the restriction of `Frob_Omega` is `Frob_E` by the M168.008 theorem
`restrictNormalHom_frobeniusAlgEquivOfAlgebraic`. Because the types of these theorems are
`Statement` definitions, each is used in the `rw` through a `show` of its unfolded equation
instead of by name alone.

## Imports and modifications

Imports: the M168.007 and M168.008 proof modules. The namespace is prefixed by `Langlands.NYLL`.
The theorem's stated type is the `Statement` target instead of the source proposition
(definitionally the same); the source `@[simp]` attribute is kept.

The original copyright and author header is retained, followed by a notice of these
modifications. Apache-2.0 attribution and notices are in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
