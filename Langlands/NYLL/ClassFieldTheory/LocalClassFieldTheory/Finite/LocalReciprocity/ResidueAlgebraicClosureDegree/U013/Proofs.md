# The fixed field of the Frobenius image (proof)

This module proves the published target
`Langlands.NYLL.LocalClassFieldTheory.fixedField_residueAbsoluteFrobeniusRangeInStatement`
(M236.013, in `ResidueAlgebraicClosureDegree/Frobenius/Statements.lean`) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.fixedField_residueAbsoluteFrobeniusRangeIn`.

Adapted by Worker 46 and Worker 721 from Naganori Yamaguchi, ClassFieldTheory (NYLL), pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
lines 181–201 (whole-file SHA-256
`650281a7282f345ec940ffcf4b5e7b794a2e18c6e34838a4def9649fe89ac2d5`). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Target

Under the source's `variable` blocks (lines 39–41), the theorem takes, in order, `k : Type u`,
`[Field k]`, `[Fintype k]`, `Omega : Type v`, `[Field Omega]`, `[Algebra k Omega]`,
`[Algebra.IsAlgebraic k Omega]` and `[IsAlgClosed Omega]`. Its type is
`fixedField_residueAbsoluteFrobeniusRangeInStatement k Omega`, which is

```lean
IntermediateField.fixedField (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊥
```

The subfield of `Omega` fixed by the image of the Frobenius homomorphism (the closed subgroup
`residueAbsoluteFrobeniusRangeIn k Omega`, M236.012) is the bottom intermediate field, that is,
the image of `k`.

## Implemented proof

The proof first installs local `have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩`
and `have : IsGalois k Omega := {}`; in the latter, instance search fills the two fields
`Algebra.IsSeparable k Omega` and `Normal k Omega`, with the local `IsAlgClosure` instance in
context. These stand in for the source's private instances M236.002 and M236.003: the source
uses the `IsGalois` instance to apply `residueAbsoluteFrobenius` and its M168.009 equation. The
M236.012 definition inlines the same values, and since both classes are propositions any two
instances agree, so the `change` step below is definitional. After `unfold` of the target, it is
the source proof, by `le_antisymm`.

1. Let `x` be in the fixed field. The arithmetic Frobenius
   `FiniteField.frobeniusAlgEquivOfAlgebraic k Omega` lies in the image: after `change` to
   membership in `(residueAbsoluteFrobenius k Omega).toMonoidHom.range`, the witness is
   `Multiplicative.ofAdd (1 : ZHat)`, and the published M168.009 theorem
   `residueAbsoluteFrobenius_one k Omega` gives its image. So by
   `IntermediateField.mem_fixedField_iff` the Frobenius fixes `x`, and the published M236.011
   theorem `mem_range_algebraMap_iff_frobenius_fixed_in` (module
   `ResidueAlgebraicClosureDegree/U011/Proofs`), with `IntermediateField.mem_bot`, puts `x` in
   `⊥`.
2. The other inclusion is `bot_le`.

No auxiliary declaration, instance or hypothesis is added.

## Modifications

- Namespace prefixed by `Langlands.NYLL`. The theorem's type is the published `Statement` rather
  than the restated proposition.
- The values of the private instances M236.002 and M236.003 come from local `have`s in the proof
  instead of the source's private section instances. M236.003 is built as `{}` from the local
  `IsAlgClosure` instance. The source's `infer_instance` would use Mathlib's
  `IsAlgClosure.isGalois`, which needs `CharZero` in the pinned Mathlib.
- An `unfold` step exposes the target before the source script.
- Imports: the published modules `ResidueAlgebraicClosureDegree/Frobenius/Statements`,
  `ResidueAlgebraicClosureDegree/U011/Proofs` (M236.011) and
  `ResidueAbsoluteFrobenius/U009/Proofs` (M168.009), in place of the NYLL source imports.
- The `open` commands are the source's (lines 26 and 34–37) without
  `open RamificationTheory.Field.absoluteGaloisGroup`, which this proof does not use.
- The theorem docstring gains the row number `(M236.013)`, and the module docstring describes this
  adaptation in place of the source file's docstring.

The original copyright and author header is retained. Apache-2.0 attribution and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
