# Intermediate-field units as fixed ambient units

The pinned original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`
(SHA-256 `392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`).
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public inventory `notes/reuse/nyll-public-port/m073-m096.md`, section M088,
records no patch10 modification of this source module. No applicable NYLL or
Yamaguchi erratum was found in the Library's `notes/errata/`.

## Exact source correspondence

| Unit and source lines | Original declaration | Public declaration |
| --- | --- | --- |
| M088.006; docstring 148–149, definition 150–162 | `LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed` |

The enclosing `noncomputable section` is source line 31. The explicit
parameters `(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]` are at line 33;
`[IsGalois K Ω]` is added at line 55. The declaration's explicit
`(E : IntermediateField K Ω)` follows those instances. Both fields have
universe zero, exactly as source `Type` specifies. There are no universe
parameters, no implicit field binders and no finiteness, perfectness,
valuation or local-field assumptions.

## Meaning and construction

For an intermediate field `E` of the Galois ambient extension `Ω/K`, the
result is the actual additive equivalence

```lean
Additive Eˣ ≃+ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
  (closedFixingSubgroup K Ω E)
```

The body is copied literally. It first forms `eRange`, the equivalence from
`Additive Eˣ` onto the range of the published inclusion
`intermediateFieldUnitsToGaloisAmbient K Ω E`, using
`AddMonoidHom.ofInjective`. Its source injectivity proof applies
`Additive.toMul.injective`, then Mathlib's `Units.map_injective E.val.injective`
to `congrArg Additive.toMul hxy`. The result is composed with
`AddEquiv.addSubgroupCongr` applied to the published range-equals-fixed-subgroup
proof `intermediateFieldUnitsToGaloisAmbient_range K Ω E` (M088.005).
Thus it uses the actual intermediate-field inclusion, representation and
closed fixing subgroup; it makes no new choices of fields or valuations.

## Reused declarations and modifications

The only import is the published
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.U005.Proofs`.
It supplies M088.005 and transitively the already published M088.001–.002
`galoisAmbientUnitsRep` and `intermediateFieldUnitsToGaloisAmbient`, M023.001
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`, and M087.001
`Langlands.NYLL.RamificationTheory.closedFixingSubgroup`. These are reused by
Lean name, not copied. Mathlib supplies the unit-map injectivity and additive
homomorphism/equivalence constructors just described. Exact-name searches of
the Library found no pre-existing definition of this equivalence; searches of
Mathlib's Galois and intermediate-field modules found no equivalence on these
NYLL fixed coefficient subgroups. The existing range proof supplies the needed
mathematics, and the new data construction preserves the source body.

Worker 324 changed only the following:

1. Extract M088.006 into the focused `AbsoluteUnitsFixedField/FixedUnitsEquiv/Definitions`
   module and prefix `LocalClassFieldTheory` with `Langlands.NYLL`.
2. Replace the source's two broad NYLL imports and Mathlib Rep import with the
   published range-proof module, which supplies their required dependencies.
3. Replace whole-file documentation with focused documentation and a modification
   notice. Keep the original declaration docstring, result type, body and embedded
   proof terms unchanged.
4. Combine the source section-variable declarations into one line without changing
   binder order or kinds, retain the noncomputable section, remove the unused
   `CyclicCohomology` namespace opening, and close the focused section/file here.

No instances or theorem proofs are introduced. The range proof is imported
from the published Library. The separate `Statements` pair records M088.007.

## Development check

Focused `lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`)
succeeded with no errors or warnings, diagnostic
`83545c67-688e-4ba1-97ff-7560e17fca4c`. Inspection reports a data definition
with an empty universe-parameter list. This is development evidence only;
independent semantic review and publication are separate requirements.

## Attribution and scope

The Lean file retains the original copyright and author header verbatim:
Copyright (c) 2026 Naganori Yamaguchi, all rights reserved; Authors: Naganori
Yamaguchi (assisted by OpenAI Codex). Apache-2.0 attribution and notices remain
in the published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 324 extracted the unit and wrote this modification record on 14 November
2026. This support unit establishes no host class-formation, cup, transfer,
Tate or reciprocity target.
