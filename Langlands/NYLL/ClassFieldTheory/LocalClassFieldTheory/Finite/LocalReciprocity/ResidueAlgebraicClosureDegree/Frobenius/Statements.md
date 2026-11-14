# Bijectivity of Frobenius on a residue algebraic closure (targets)

Adapted by Worker 46 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`
(whole-file SHA-256 `650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M236.010 | `residueAbsoluteFrobenius_isAlgClosure_injective` (112–143) | `residueAbsoluteFrobenius_isAlgClosure_injectiveStatement` |
| M236.013 | `fixedField_residueAbsoluteFrobeniusRangeIn` (181–201) | `fixedField_residueAbsoluteFrobeniusRangeInStatement` |
| M236.014 | `residueAbsoluteFrobeniusRangeIn_eq_top` (203–210) | `residueAbsoluteFrobeniusRangeIn_eq_topStatement` |
| M236.015 | `residueAbsoluteFrobenius_isAlgClosure_surjective` (212–220) | `residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`. Every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

## Content

Let `k : Type u` be a field with `[Fintype k]`, and let `Omega : Type v` be a `k`-algebra field
with `[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`, i.e. an algebraic closure of the
finite field `k`. Let `residueAbsoluteFrobenius k Omega : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega)` be the
canonical Frobenius-parameter homomorphism (M168.005), and let
`residueAbsoluteFrobeniusRangeIn k Omega` be its range as a closed subgroup (M236.012).

- M236.010: `residueAbsoluteFrobenius k Omega` is injective (`Function.Injective`).
- M236.013: the fixed field of the range, `IntermediateField.fixedField` of
  `(residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup`, is `⊥`, i.e. exactly `k`.
- M236.014: the range is the whole Galois group:
  `(residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤`.
- M236.015: `residueAbsoluteFrobenius k Omega` is surjective (`Function.Surjective`).

None of the four source theorems has an `omit`, so each takes the full section telescope, in
order: `k`, `[Field k]`, `[Fintype k]`, `Omega`, `[Field Omega]`, `[Algebra k Omega]`,
`[Algebra.IsAlgebraic k Omega]`, `[IsAlgClosed Omega]`. A development `#check` confirmed that
each `Statement` has exactly this parameter list. Every binder is used, through
`residueAbsoluteFrobeniusRangeIn` or through the inlined `IsGalois` instance below.

## Modifications

- The namespace is prefixed by `Langlands.NYLL`. Each source theorem is replaced by a Prop-valued
  definition with the `Statement` suffix whose body is the source proposition. They sit under the
  source's `variable` blocks (lines 39–41) with the source's universes and `open` commands, except
  the dropped NYLL `open RamificationTheory.Field.absoluteGaloisGroup`, which is unused here.
  Source proofs are omitted, so nothing is proved here.
- Private instances M236.002 and M236.003. In the source, `residueAbsoluteFrobenius k Omega`
  (which needs `[IsGalois k Omega]`) receives the private section instance
  `residueAlgebraicClosureIsGalois`, built from `residueAlgebraicClosureIsAlgClosure`. No instance
  is declared here. The targets of M236.010 and M236.015 start with
  `haveI : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩` (the M236.002 value) and
  `haveI : IsGalois k Omega := {}`. The latter stands for M236.003: the source proves it by
  `infer_instance`, but in the pinned Mathlib of this environment `IsAlgClosure.isGalois` requires
  `[CharZero k]`, so the structure instance fills `Algebra.IsSeparable k Omega` and
  `Normal k Omega` by instance search. `haveI` substitutes these values into the elaborated
  proposition and leaves no binder. Since `IsGalois k Omega` is a proposition, any instance a
  consumer has is definitionally equal to this one. The targets of M236.013 and M236.014 mention
  only `residueAbsoluteFrobeniusRangeIn`, which inlines its own instances.
- Imports: the sibling `Frobenius/Definitions` module, which imports the published port of
  `residueAbsoluteFrobenius`.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. This support unit makes no claim to discharge
the host class-formation, cup, transfer, Tate or reciprocity targets.
