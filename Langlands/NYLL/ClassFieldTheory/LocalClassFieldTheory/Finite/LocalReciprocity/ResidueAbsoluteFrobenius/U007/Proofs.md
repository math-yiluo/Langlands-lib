# M168.007: `restrictNormalHom_residueAbsoluteFrobenius_one` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_residueAbsoluteFrobenius_oneStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_residueAbsoluteFrobenius_one`,
whose type is the target applied to the source parameters, under the source's `variable` block
(so its binders are those of the target in the same order), followed by `E`.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`,
lines 126–136. Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

The source proof, with the `Statement` definitions unfolded first. Unfold the target; take the
M168.006 theorem `restrictNormalHom_residueAbsoluteFrobenius` at `z = ofAdd 1` and `E`, unfold
its `Statement` type, and rewrite with it. The goal becomes
`finiteResidueFrobeniusIntermediate k Omega E (ofAdd 1) = Frob_E`. The M168.001 definition
`finiteResidueFrobeniusIntermediate k Omega E` is `finiteResidueFrobeniusFromZHat k E` under the
local instance `Finite E` given by `Module.finite_of_finite k`. With the same local instance
introduced by `let`, the goal is definitionally the M167.013 theorem
`finiteResidueFrobeniusFromZHat_one k E` (whose `abbrev` target is
`finiteResidueFrobeniusFromZHat k E (ofAdd 1) = Frob_E`), which closes it by `exact`.

## Imports and modifications

Imports: the M168.006 proof module and the M167.013 proof module
(`...FiniteResidueFrobenius.U013.Proofs`). The namespace is prefixed by `Langlands.NYLL`. The
theorem's stated type is the `Statement` target instead of the source proposition
(definitionally the same); the `unfold` steps replace the source's direct `rw`, which cannot see
through the `Statement` definition of the M168.006 theorem's type.

The original copyright and author header is retained, followed by a notice of these
modifications. Apache-2.0 attribution and notices are in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
