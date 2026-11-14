# Absolute Frobenius action: restriction and the exponent one (targets)

Adapted by Worker 123 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration | Source `@[simp]` |
| --- | --- | --- | --- |
| M168.006 | `restrictNormalHom_residueAbsoluteFrobenius` (115–124) | `restrictNormalHom_residueAbsoluteFrobeniusStatement` (`def`) | no |
| M168.007 | `restrictNormalHom_residueAbsoluteFrobenius_one` (126–136) | `restrictNormalHom_residueAbsoluteFrobenius_oneStatement` (`def`) | no |
| M168.009 | `residueAbsoluteFrobenius_one` (161–177) | `residueAbsoluteFrobenius_oneStatement` (`abbrev`) | yes |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Throughout, `k : Type u` is a field with `[Fintype k]` and `Omega : Type v` is
a field with a `k`-algebra structure and `[IsGalois k Omega]`;
`residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)` is the
published M168.005 definition and `Frob_X = FiniteField.frobeniusAlgEquivOfAlgebraic k X`
is Mathlib's arithmetic Frobenius `x ↦ x ^ #k` of an algebraic extension `X` of `k`.

- M168.006: for `z : ZHatMul` and `E : FiniteGaloisIntermediateField k Omega`,
  `AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega z)` equals the
  published M168.001 `finiteResidueFrobeniusIntermediate k Omega E z`: the
  restriction to `E` of the absolute action of `z` is the finite Frobenius
  action of `z` on `E`.
- M168.007: for every `E`, the restriction to `E` of
  `residueAbsoluteFrobenius k Omega (Multiplicative.ofAdd 1)` is `Frob_E`.
- M168.009: `residueAbsoluteFrobenius k Omega (Multiplicative.ofAdd 1) = Frob_Omega`.

Each target's parameters are, in order, `k`, `Omega`, `[Field k]`, `[Fintype k]`,
`[Field Omega]`, `[Algebra k Omega]`, `[IsGalois k Omega]` and then the row's own
arguments (`z`, `E` for M168.006; `E` for M168.007; none for M168.009), those of
the source theorems: each statement mentions `residueAbsoluteFrobenius k Omega`,
which uses every section binder.

## Modifications

- Namespace prefixed by `Langlands.NYLL`; each source theorem is replaced by a
  Prop-valued definition with the `Statement` suffix whose body is the source
  proposition verbatim. The target of the source `@[simp]` theorem M168.009 is
  an `abbrev`, so that the eventual theorem can carry `@[simp]`; the other two
  are `def`s. Source proofs are omitted; nothing is proved here.
- The source `variable` block (lines 35–37), universes, `open` commands and
  `noncomputable section` are retained.
- Imports: the sibling `Absolute/Definitions` module (M168.003/.005).
- M168.008 has its target in the published `Initial/Statements` module;
  M168.004 is outside Task 5860.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
