# Base-field units as Galois-fixed ambient units

The pinned original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`
(SHA-256 `b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`).
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The inventory `notes/reuse/nyll-public-port/m073-m096.md`, section M096,
records no patch10 modification of this file. No applicable NYLL or Yamaguchi
erratum was found in the Library's `notes/errata/`.

## Exact source correspondence and interface

| Unit and lines | Original declaration | Public declaration |
| --- | --- | --- |
| M096.001; docstring 39–40, definition 41–50 | `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` | `Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` |

The source's noncomputable section starts at line 32. The complete parameter
order, from source lines 36–37, is unchanged:

```lean
(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
```

Both fields are explicit and universe zero. There is no intermediate-field
parameter, finite-dimensional hypothesis, perfectness hypothesis, valuation
or local-field data. The result is

```lean
Additive Kˣ ≃+ ambientFixedAddSubgroup
  (galoisAmbientUnitsRep K Ω)
  (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
```

## Meaning and unchanged construction

The bottom intermediate field is the embedded base field in `Ω`. The body
first sets `eBot` to the additive form of the unit equivalence induced by
`(IntermediateField.botEquiv K Ω).symm`, using exactly the source expression
`MulEquiv.toAdditive (Units.mapEquiv (IntermediateField.botEquiv K Ω).symm.toMulEquiv)`.
It then composes `eBot` with
`intermediateFieldUnitsEquivGaloisFixed K Ω ⊥` (M088.006). This identifies base
units with the coefficient subgroup fixed by the bottom field's actual
closed fixing subgroup. The construction and its entire term are copied
literally, including the orientation of `botEquiv` and both equivalences.
The docstring's absolute-Galois wording is inherited from the source; the
actual interface permits any Galois ambient extension, including infinite
ones, and does not assert that `Ω` is a separable closure.

## Reuse and complete modification record

The only import is the focused
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions`.
It supplies M088.006 and transitively the published ambient-unit
representation, intermediate-field unit inclusion, fixed additive subgroup
and closed fixing subgroup. Mathlib's `IntermediateField.botEquiv`,
`Units.mapEquiv`, `MulEquiv.toAdditive` and `AddEquiv.trans` provide the other
constructors. All these are reused by Lean name. Exact-name Library and
Mathlib searches found no existing definition of this NYLL fixed-unit
equivalence; the bottom-field and unit equivalences are the existing data
reused in its source construction.

Worker 324 extracted M096.001 to `SeparableUnitsNorm/BaseUnits/Definitions`
and prefixed the enclosing namespace with `Langlands.NYLL`. The source's
Mathlib norm-transitivity import and three broad NYLL imports are replaced
by the one focused import above. Whole-file documentation is replaced by
focused documentation and a modification notice. The `LocalFieldTheory`,
`ClassFormation` and `CyclicCohomology` namespace openings and
`open scoped BigOperators` are omitted because this unit does not use them.
The original declaration docstring, all parameters, binder kinds, result type,
noncomputable section and complete body are retained unchanged. No instance,
proof or additional hypothesis is introduced. Other source units are outside
this definition pair.

## Development check

Focused `lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`)
succeeded with no errors or warnings, diagnostic
`939622f7-35fa-48e0-b157-68465029389d`. Inspection confirms a data definition
with no universe parameters. Independent review and publication remain separate.

## Attribution and scope

The original copyright and author header is retained verbatim in the Lean
file: Copyright (c) 2026 Naganori Yamaguchi, all rights reserved; Authors:
Naganori Yamaguchi (assisted by OpenAI Codex). The published
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain the Apache-2.0 license
and notices. Worker 324 extracted the units and wrote this modification record
on 14 November 2026. This support work discharges no host class-formation,
cup, transfer, Tate or reciprocity target.
