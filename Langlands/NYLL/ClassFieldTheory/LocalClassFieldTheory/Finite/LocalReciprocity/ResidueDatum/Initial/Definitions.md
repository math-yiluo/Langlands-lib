# The residue datum

This module adapts exactly M238.001 from Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean#L35-L39),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The definition with its
documentation string is at lines 35–39. The section variables it uses are at
lines 31–33, the imports at lines 7–9, and the namespace, `open` commands and
`noncomputable section` at lines 22–29 and 120–121. The original file has
121 lines and SHA-256
`0ffd3ceea309047d8e54275d4680c8c86ea3dd071ad786a71df35f18642bfbdf`.
Its other declarations are the private lemma M238.002 (lines 41–63) and the
theorems M238.003 (lines 65–107) and M238.004 (lines 109–118). The targets of
the two theorems are in the sibling
[`Statements.lean`](Statements.lean).

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source
path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's port plan lists this row as M238.001 (family `N`, no patch10
change) in `notes/reuse/nyll-public-port/m217-m240.md`. The work is part of
Task 5862.

## Interface and meaning

The complete interface, with namespace `Langlands.NYLL.LocalClassFieldTheory`
and `Langlands.NYLL.ClassFormation` open, is:

```lean
variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

noncomputable def residueDatumIn : DegreeData (Omega ≃ₐ[k] Omega) where
  degree := residueAbsoluteDegreeIn k Omega
  degree_surjective := (residueAbsoluteFrobeniusEquivIn k Omega).symm.surjective
```

The arguments are `k` and `Omega`, both explicit and both in `Type` (universe
level 0, as in the source). Then come the instances of the source's section
variables, in their order: `k` is a finite field (`Field k`, `Fintype k`),
`Omega` is a field with a `k`-algebra structure, `Omega` is algebraic over `k`,
and `Omega` is algebraically closed. In other words, `Omega` is an algebraic
closure of the finite field `k`. The definition has no universe level
parameters (`lean_check` reports `[]`). All six instances stay arguments: the
body applies `residueAbsoluteDegreeIn k Omega`, whose own binders are exactly
these six instances, so none of them is unused.

The value is a `DegreeData` on the group `Omega ≃ₐ[k] Omega` of
`k`-automorphisms of `Omega`, with Mathlib's Krull topology. The Library's
`Langlands.NYLL.ClassFormation.DegreeData G`
(`Langlands/NYLL/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields/Definitions.lean`,
the adaptation of NYLL M010) has two fields:

- `degree : G →ₜ* ZHatMul`, a continuous homomorphism to
  `ZHatMul = Multiplicative ZHat`, the profinite integers written
  multiplicatively;
- `degree_surjective : Function.Surjective degree`.

Here `degree` is `residueAbsoluteDegreeIn k Omega`, the inverse of the
arithmetic Frobenius coordinates `residueAbsoluteFrobeniusEquivIn k Omega :
ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega)`, recast as a continuous monoid homomorphism.
It sends the arithmetic Frobenius automorphism to the generator
`Multiplicative.ofAdd 1`. The surjectivity field is the surjectivity of the
inverse equivalence. So `residueDatumIn k Omega` is the "initial datum" of the
abstract class-formation framework that Frobenius supplies on the Galois group
of an algebraic closure of a finite field.

Both reused declarations are the Task 5860 adaptations of NYLL M236.017 and
M236.016 from
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean`,
lines 241 and 224, published as
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteDegreeIn` and
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobeniusEquivIn` in
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree/Equiv/Definitions.lean` (accepted artifact `3c8deff0-1cf4-47f3-bf09-1bda6b157b51`, Task 5860). The definition restates neither of them.

The source definition has no attribute. It is `noncomputable` inside the
source's `noncomputable section`, and both are kept.

## Exact declaration map and modifications

| Source declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.residueDatumIn` (M238.001) | `Langlands.NYLL.LocalClassFieldTheory.residueDatumIn` |

The only changes are these:

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`, and the opened namespace
  `ClassFormation` becomes `Langlands.NYLL.ClassFormation`. The source line
  `open RamificationTheory` is dropped. The definition uses nothing from that
  namespace, and none of this file's imports declares
  `Langlands.NYLL.RamificationTheory`, so the `open` command would fail. The
  `Statements` file, which imports `closedFixingSubgroup`, keeps it.
- The definition moves from the source module to
  `Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum/Initial/Definitions.lean`.
  The source theorems M238.003/.004 are stated in the sibling `Statements`
  file and the private lemma M238.002 is not part of this module (see
  [`Statements.md`](Statements.md)).
- The three NYLL imports are replaced. The import of NYLL M237
  (`ResidueAlgebraicallyClosed`) is replaced by the Library module
  `Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree/Equiv/Definitions.lean`, which
  publishes `residueAbsoluteDegreeIn` and `residueAbsoluteFrobeniusEquivIn`.
  No declaration of M237 (`valuationSubring_residueField_isAlgClosed`,
  `valuationSubringComapMap`, `valuationSubringComapMap_isLocalHom`,
  `valuationSubringComapResidueMap`,
  `valuationSubring_comap_residueField_isPurelyInseparable`) occurs in
  M238; the source imports M237 only for its transitive import of M236.
  The import of NYLL M010 (`AbstractClassFieldTheory.Degree.Fields`) becomes
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`.
  The import of NYLL M087 (`ClosedFixingSubgroup`) is needed only by the
  theorems, so it moved to the `Statements` file.
- The module documentation keeps the first sentence of the original and adds
  the adaptation record.

The binders, universes, documentation string, result type, `noncomputable`
status and body are unchanged. No proof, placeholder proposition or instance
is added. `lean_check` `71b5331c-0cc8-4700-aaa9-2cb4e27211d7` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), against Library
`2016a0d994180c702214a75514a08546aa930f07`, compiled the module with 0 errors
and 0 warnings. Its inspection of `residueDatumIn` reports kind `definition`,
level parameters `[]`, and the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are kept
unchanged. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 59 checked the original source and the reused Library declarations,
implemented this focused extraction and wrote this documentation in
November 2026. The Lean header records the modifications.
