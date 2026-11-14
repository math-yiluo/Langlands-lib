# Base-unit value and intermediate-field coset-action targets

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

## Exact source correspondence

| Unit and lines | Original theorem | Public proposition definition |
| --- | --- | --- |
| M096.002; docstring 52, attribute 53, theorem type 54–57, proof 57–58 | `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val` | `Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_valStatement` |
| M096.004; omission 75, docstring 76, theorem type 77–91, proof 91–117 | `LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val` | `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_valStatement` |

Both propositions retain the source parameter order from lines 36–37:

```lean
(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
```

Both field parameters are explicit, universe zero, with no universe parameters.
M096.002 adds only `(x : Kˣ)`. M096.004 then adds
`(E : IntermediateField K Ω) [IsGalois K E] (x : Eˣ) (q : Q)`, in that order,
where the actual source quotient `Q` is

```lean
(closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
  extensionSubgroup
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
```

The source section at line 62 also declares `[FiniteDimensional K E]`, but
source line 75 explicitly omits it for M096.004. The port retains that
`omit` command. Thus this target makes no finite-dimensional assumption.
It retains both Galois hypotheses. No quotient-finiteness instance is
required by this statement.

## Propositions and mathematical meaning

M096.002 asserts that the value in `Ω` of the base-unit fixed-subgroup
equivalence is the original unit's image under `algebraMap K Ω`:

```lean
((Additive.toMul
  ((baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul x)).1 :
    Additive Ωˣ) : Ωˣ) : Ω) = algebraMap K Ω (x : K)
```

M096.004 asserts the exact equality

```lean
((Additive.toMul
  (relativeCosetAction (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
    (intermediateFieldUnitsEquivGaloisFixed K Ω E
      (Additive.ofMul x)) q) : Ωˣ) : Ω) =
  E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E q) (x : E))
```

It compares the actual ambient coefficient coset action with the
corresponding automorphism of `E/K`, evaluated on the unit's field value and
included into `Ω`. Both bodies are the source statements literally, with
source names resolving in `Langlands.NYLL`. These are proposition definitions
only; neither source theorem proof is included.

## Reuse, imports and modifications

The focused imports are:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions`,
  supplying M096.001 and transitively M088.006 and its fixed-unit dependencies;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions`,
  supplying published M089.011 `baseFixingExtensionQuotientEquivGaloisGroup`,
  M089.002 `fixingSubgroupLeBase`, and the published extension-subgroup alias;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions`,
  supplying published M024.001 `Langlands.NYLL.ClassFormation.relativeCosetAction`.

The published coset-action interface uses Mathlib's
`L.toSubgroup.subgroupOf K.toSubgroup` directly for the quotient subgroup;
this is definitionally the body of the published
`Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK`. The source
statement's `extensionSubgroup` spelling is retained without a rewrite or
substitute. All referenced Library and Mathlib constants are reused by Lean
name. Exact-name Library/Mathlib searches found no existing statements with
these NYLL equivalences and action.

Worker 324 extracted just M096.002 and .004 into the focused `BaseUnits/Statements`
module, prefixed the namespace with `Langlands.NYLL`, changed each `theorem`
into `def ... : Prop :=`, and appended `Statement`. The source proofs are
omitted; the source `@[simp]` on M096.002 is omitted because this file defines
a proposition, and both theorem docstrings are replaced by proposition-specific
docstrings. No equality, coercion, parameter, binder kind or hypothesis in
the source theorem types is changed. The source section and finite-dimensional
omission for M096.004 remain, as does the noncomputable section. The source
broad imports and whole-file documentation are replaced by the imports and
focused documentation above; unused `LocalFieldTheory` and `BigOperators`
openings are omitted, while `ClassFormation CyclicCohomology` is opened only
for the coset-action target. No new instance or proof is introduced. M096.003,
already published separately, is neither duplicated nor required here.

## Development checks

Focused `lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`)
compiled this module without errors or warnings. Exact inspections
`e5d4d6b8-1f30-4c66-900b-19d68c5f96c4` (M096.002) and
`ef4d90e2-5e70-412b-b360-e13f80a70814` (M096.004) each explicitly report
`statement_returns_prop: true` and an empty universe-parameter list.
These checks are development evidence only; independent review and
publication are separate requirements.

## Attribution and scope

The original copyright and author header is retained verbatim in the Lean
file: Copyright (c) 2026 Naganori Yamaguchi, all rights reserved; Authors:
Naganori Yamaguchi (assisted by OpenAI Codex). The published
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain the Apache-2.0 license
and notices. Worker 324 extracted the units and wrote this modification record
on 14 November 2026. This support work discharges no host class-formation,
cup, transfer, Tate or reciprocity target.
