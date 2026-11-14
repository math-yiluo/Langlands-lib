# Abstract fixed-field relative norm: value target

This module defines the proposition
`Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement`.
It publishes a target for a later proof; it does not prove the norm identity.

## Pinned source and declaration map

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`.
The source file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`;
its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the registered supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Adapted declaration |
| --- | --- | --- |
| M300.006 | `LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGalois`, lines 149–197; signature 149–166 | `Langlands.NYLL.LocalClassFieldTheory.relativeNorm_abstractFixedFieldUnit_val_of_isGaloisStatement` |

The section parameter at source line 32 supplies explicit `(K : Type)` and
`[Field K]`. The declaration keeps, in order, explicit `H`, explicit subgroup
inclusion `hH`, the finite relative-coset-quotient instance, the
finite-dimensional instance, the Galois instance, and explicit unit `x`.
The ground field and separable closure remain in universe zero.

## Exact mathematical content

Write `E := abstractFixedField K (SeparableClosure K) H`. This is the actual
intermediate fixed field of `H.toSubgroup` in the chosen separable closure.
The hypotheses are precisely

```lean
(K : Type) [Field K]
(H : ClosedSubgroup (intrinsicAbsoluteGalois K))
(hH : H.toSubgroup ≤ (intrinsicAbstractBase K).toSubgroup)
[Finite ((intrinsicAbstractBase K).toSubgroup ⧸
  extensionSubgroup (intrinsicAbstractBase K) H hH)]
[FiniteDimensional K (abstractFixedField K (SeparableClosure K) H)]
[IsGalois K (abstractFixedField K (SeparableClosure K) H)]
(x : (abstractFixedField K (SeparableClosure K) H)ˣ)
```

Apply `abstractFixedFieldUnitsEquivGaloisFixed` to `Additive.ofMul x`, then the
actual class-formation homomorphism `relativeNorm (intrinsicAbsoluteUnits K)
(intrinsicAbstractBase K) H hH`. The proposition says that the resulting
fixed coefficient, projected to its underlying additive unit, converted by
`Additive.toMul`, and coerced first to a unit and then to an element of
`SeparableClosure K`, equals
`algebraMap K (SeparableClosure K) (Algebra.norm K (x : E))`.
The Lean body retains every source projection, type annotation and coercion.
There is no local-field hypothesis or supplied norm identity.

## Reused objects and proof boundary

The imports reuse these names under their support paths:

| Declaration | Support module |
| --- | --- |
| `Langlands.NYLL.ClassFormation.relativeNorm` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions` |
| `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois`, `intrinsicAbsoluteUnits`, `intrinsicAbstractBase` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions` |
| `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` (imported transitively) |
| `Langlands.NYLL.CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |

`Algebra.norm`, `SeparableClosure`, the field structures and coercions are
Mathlib objects. None is reconstructed or replaced. The class-formation norm
is a coset-sum homomorphism on the actual fixed additive coefficient groups;
on additive unit groups that sum represents a product.

The original proof at lines 167–197 transports the intermediate-field unit
norm identity across equality of the closed fixing subgroup with `H`.
It uses `relativeNorm_intermediateFieldUnit_val_of_isSeparable`,
`relativeNorm_coe_eq_of_closedSubgroup_eq`,
`closedFixingSubgroup_abstractFixedField_eq` and the two fixed-unit coercion
lemmas. Those are dependencies of a future exact proof, not hypotheses or
imports required to state this proposition.

## Modifications and attribution

Worker 537 made only the following modifications:

1. Prefix the source namespace by `Langlands.NYLL` and suffix the theorem
   name by `Statement`.
2. Replace `theorem ... : conclusion := by ...` by
   `def ... : Prop := conclusion`, omitting the entire proof.
3. Move the source section binders `(K : Type) [Field K]` into the declaration
   explicitly, retaining their order and binder kinds.
4. Replace the five broad upstream imports by four focused support imports.
   Retain the namespace openings needed by the unchanged conclusion and
   telescope, and omit unused openings and unrelated declarations.
5. Replace the source module documentation and theorem docstring with target
   documentation and this modification record. Keep the noncomputable section.

The original Apache-2.0 copyright and author header is retained verbatim.
The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained
without modification. Their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
