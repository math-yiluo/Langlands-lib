# M168.006: `restrictNormalHom_residueAbsoluteFrobenius` (proof)

Proves the published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_residueAbsoluteFrobeniusStatement` as
`theorem Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_residueAbsoluteFrobenius`,
whose type is the target applied to the source parameters, under the source's `variable` block
(so its binders, including `[IsGalois k Omega]`, are those of the target in the same order),
followed by `z` and `E`.

Adapted from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`,
lines 115–124. Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Proof

The source proof, unchanged. `residueAbsoluteFrobenius k Omega z` is by definition
`(InfiniteGalois.continuousMulEquivToLimit k Omega).symm (residueFrobeniusToLimit k Omega z)`.
Applying `continuousMulEquivToLimit` to it gives back `residueFrobeniusToLimit k Omega z`
(`apply_symm_apply`); taking the coordinate at `op E` of both sides gives the target, because
the coordinate of `continuousMulEquivToLimit σ` at `E` is `AlgEquiv.restrictNormalHom E σ` and
the coordinate of `residueFrobeniusToLimit k Omega z` at `E` is
`finiteResidueFrobeniusIntermediate k Omega E z`, both definitionally. The resulting equation is
closed by `exact`, which unfolds the `Statement` definition.

## Imports and modifications

Imports: the target module `...ResidueAbsoluteFrobenius.Absolute.Statements`. The namespace is
prefixed by `Langlands.NYLL`. The theorem's stated type is the `Statement` target instead of the
source proposition (definitionally the same).

The original copyright and author header is retained, followed by a notice of these
modifications. Apache-2.0 attribution and notices are in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
