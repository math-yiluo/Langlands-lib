# Restriction of the absolute Frobenius to finite Galois subextensions (target)

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M168.008 | `restrictNormalHom_frobeniusAlgEquivOfAlgebraic` (138–159) | `restrictNormalHom_frobeniusAlgEquivOfAlgebraicStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

For a field `k : Type u` with `[Fintype k]`, a Galois `k`-algebra field
`Omega : Type v` (`[IsGalois k Omega]`) and
`E : FiniteGaloisIntermediateField k Omega`, the target states that
`AlgEquiv.restrictNormalHom E` sends the arithmetic Frobenius
`FiniteField.frobeniusAlgEquivOfAlgebraic k Omega` of `Omega` to the
arithmetic Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic k E` of `E`.
Its parameters are, in order, `k`, `Omega`, `[Field k]`, `[Fintype k]`,
`[Field Omega]`, `[Algebra k Omega]`, `[IsGalois k Omega]` and `E`, those of the
source theorem.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; the source theorem is replaced by a
  Prop-valued definition with the `Statement` suffix whose body is the source
  proposition verbatim. The source proof is omitted; nothing is proved here.
- The source `variable` block (lines 35–37), universes, `open` commands and
  `noncomputable section` are retained. The statement uses every section binder
  (`[IsGalois k Omega]` supplies the algebraicity needed by
  `FiniteField.frobeniusAlgEquivOfAlgebraic k Omega`), so the parameter list is
  that of the source theorem (checked with `#check`).
- Imports: the sibling `Initial/Definitions` module, which supplies the Mathlib
  Galois and finite-field API.
- The source theorems M168.006, M168.007 and M168.009 mention the later data
  command M168.005 and are not part of this module.

A private probe (not part of this unit) proves the target with the source
proof.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
