# Unit-factor identity, product and integer-unit targets (M376.002–.004)

This module defines three closed propositions in
`Langlands.NYLL.LocalFieldTheory`. For every field `K : Type u` in an arbitrary
universe, with instances `[Field K]`, `[ValuativeRel K]`, `[TopologicalSpace K]`
and `[IsNonarchimedeanLocalField K]`, fix `pi : Kˣ` and
`hpi : valuationMap K (Additive.ofMul pi) = 1`. Then the targets say:

- `uniformizerUnitFactor_oneStatement`: the unit factor of `1 : Kˣ` is
  `1 : 𝒪[K]ˣ`.
- `uniformizerUnitFactor_mulStatement`: for every `x y : Kˣ`, the unit factor
  of `x * y` equals the product of their unit factors in `𝒪[K]ˣ`.
- `uniformizerUnitFactor_integerUnitStatement`: for every `u : 𝒪[K]ˣ`, the unit
  factor of its image under `integerUnitsToFieldUnits K` is `u` itself.

These are statement definitions, not proofs of the three laws. The module
introduces no data, instances or theorem declarations.

## Complete propositions

The following is the complete mathematical content of the Lean module:

```lean
open scoped ValuativeRel

namespace Langlands.NYLL.LocalFieldTheory

open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- M376.002: the unit factor of one is one. -/
def uniformizerUnitFactor_oneStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : Kˣ)
    (hpi : IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul pi) = 1),
    IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi 1 = 1

/-- M376.003: the unit factor preserves multiplication. -/
def uniformizerUnitFactor_mulStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : Kˣ)
    (hpi : IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul pi) = 1)
    (x y : Kˣ),
    IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi (x * y) =
      IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi x *
        IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi y

/-- M376.004: the unit factor of an embedded integer unit recovers that unit. -/
def uniformizerUnitFactor_integerUnitStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : Kˣ)
    (hpi : IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul pi) = 1)
    (u : 𝒪[K]ˣ),
    IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi
        (integerUnitsToFieldUnits K u) = u

end Langlands.NYLL.LocalFieldTheory
```

Every definition has type `Prop` with no term parameters outside its body and
one universe parameter `u`. Each body universally quantifies, in order, the
explicit field `K`, the four instance arguments, the explicit field unit `pi`,
the explicit proof `hpi`, and then `x y : Kˣ` or `u : 𝒪[K]ˣ` where present.
There are no source section variables to recover: the source's local opens
and namespace are at lines 18–25, and each theorem supplies its own telescope.
The explicit `Type u` preserves the source's arbitrary `Type*`; it does not
specialize the field to universe zero. The equality in each body is exactly
the corresponding source theorem's conclusion after namespace adaptation.

## Actual maps and valuation convention

The module imports the published definitions directly:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U027.Definitions`
  supplies
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor`
  (M134.038), using its actual valuation-ring-unit construction. Its transitive
  imports supply
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`
  (M134.002), of type `Additive Kˣ →+ ℤ`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`
  supplies
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits`
  (M128.016), the actual `Units.map (algebraMap 𝒪[K] K).toMonoidHom`.
  The source's unqualified `integerUnitsToFieldUnits` resolves in the open
  `LocalFieldTheory.IsNonarchimedeanLocalField` namespace; this module keeps
  that open after prefixing it with `Langlands.NYLL`. Thus the shorter name
  denotes the published inclusion above; no alias or replacement is defined.

Mathlib supplies `𝒪[K]`, scoped in `ValuativeRel`, as the valuation ring, and
`𝒪[K]ˣ` as its group of units. The actual factor is the unit with underlying
field element `x / pi ^ valuationMap K (Additive.ofMul x)`.

NYLL's `valuationMap` is the **negative** of the usual normalized discrete
order. A prime element of `𝒪[K]` has NYLL value `-1`; hence `hpi` makes `pi`
an **inverse uniformizer**, whose inverse has usual order one. The source
names are retained. This convention is explained in the imported U027
`Definitions.md` and the published
[finite-reciprocity source audit](../../../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md),
section 2.3. The source `IdealQuotients.lean`, lines 210–244, gives the prime
and inverse-prime values. The three targets do not change the supplied
normalization or require a new uniformizer choice.

The source proofs use an injectivity helper (M376.001) and the specification
of the unit factor (M134.039). Those proofs are omitted here; neither result
is needed to formulate these targets. M134.040 and the later quotient maps
M376.005–.008 are also outside this module.

## Source correspondence

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UniformizerPrincipalQuotient.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UniformizerPrincipalQuotient.lean),
SHA-256 `6952bb5c650357c8c02c67a668135ee6882516bcd23f84f37cd672230cbdc9bc`.
The readable pinned copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The published [partition](../../../../../../notes/reuse/nyll-public-port/m361-m384.md#m376)
identifies these units. No matching NYLL erratum was found in the Library's
`notes/errata/`.

| Unit | Original theorem in `LocalFieldTheory` | Source type lines | Adapted definition in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M376.002 | `uniformizerUnitFactor_one` | 36–41 | `uniformizerUnitFactor_oneStatement` |
| M376.003 | `uniformizerUnitFactor_mul` | 49–57 | `uniformizerUnitFactor_mulStatement` |
| M376.004 | `uniformizerUnitFactor_integerUnit` | 67–74 | `uniformizerUnitFactor_integerUnitStatement` |

The source docstrings are at lines 34–35, 47–48 and 65–66. The proof bodies
at lines 41–45, 57–63 and 74–81 are not extracted. The original imports are
`StandardOpenSubgroups` and `ValuationExactSequence`; the two focused published
imports above suffice for the conclusions and their complete hypotheses.

## Adaptation and attribution

Worker 330 adapted these three types directly from the pinned source on
16 November 2026. The modifications are: add the namespace prefix
`Langlands.NYLL`; append `Statement` to each theorem name; replace each
`theorem` and its proof by a closed `def ... : Prop := ∀ ...`; spell out the
source's arbitrary field universe as `u`; shorten namespace qualifications
within the adapted namespace without changing the resolved declarations;
replace the broad source imports by the two focused imports; and replace
the source theorem docstrings by target descriptions. All original binder
kinds, their order, hypotheses and conclusions are retained. The original
proofs and every other source declaration are omitted.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. A separate Lean comment records these
modifications. The unchanged
[LICENSE](../../../../../../licenses/NYLL/LICENSE), SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and
[NOTICE](../../../../../../licenses/NYLL/NOTICE), SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`, remain
in `licenses/NYLL/` and match the pinned originals.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No other worker supplied new code for this adaptation; published imports
retain their own authorship.

## Development checks

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the complete module
compiled with zero errors and zero warnings. Separate declaration inspections
reported `kind: definition`, `statement_returns_prop: true` and the single
universe parameter `u` for each target:

| Target suffix | Diagnostic ID |
| --- | --- |
| `oneStatement` | `9d840184-654f-406b-8484-fa002745554f` |
| `mulStatement` | `61ba4dc9-5a50-4db2-85a0-e713942cb324` |
| `integerUnitStatement` | `a422a6a0-d6d2-4172-a5b0-317d4fbac02e` |

These are development checks, not independent semantic acceptance or proofs
of the three propositions.
