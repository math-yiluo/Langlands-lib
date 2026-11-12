# Targets for the valuation-integer unit subgroup

This module defines two unproved propositions about the published
`Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup`. That subgroup is the
image of the canonical inclusion `𝒪[K]ˣ →* Kˣ`, using Mathlib's valuation-integer
subring. Both definitions preserve the arbitrary source universe `u`.

The full interfaces and proposition bodies are:

```lean
def Langlands.NYLL.LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_oneStatement
    (K : Type u) [Field K] [ValuativeRel K] (x : Kˣ) : Prop :=
  x ∈ Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup K ↔
    ValuativeRel.valuation K (x : K) = 1

def Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup_isOpenStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
  IsOpen (Langlands.NYLL.LocalFieldTheory.localBaseUnitSubgroup K : Set Kˣ)
```

The first target says that a field unit is in the image precisely when its
canonical multiplicative valuation is one. `K` and `x` remain explicit; no
topology or local-field hypothesis is required. The second target says that
this subgroup is open in the usual topology on the unit group induced by the
supplied topology on `K`. It retains the source's `Field`, `ValuativeRel`,
`TopologicalSpace` and Mathlib `IsNonarchimedeanLocalField` instances in that
order, with explicit `K`. Neither proposition is proved in this module.

## Source correspondence

The original is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean>).
Its SHA-256 is
`77d63306c40bd28166878221e43427bbbcd699daeee497bbe40c82935d928f43`.
The universe, namespace and opened namespaces are at source lines 19–26.

| Source unit and original name | Original lines | Public target in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- |
| M256.002, `LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_one` | 33–59; declaration at 35–37 | `mem_localBaseUnitSubgroup_iff_valuation_eq_oneStatement` |
| M256.003, `LocalFieldTheory.localBaseUnitSubgroup_isOpen` | 61–77; declaration at 63–66 | `localBaseUnitSubgroup_isOpenStatement` |

The original module and its complete imported NYLL Basic file were read. Each
target body is exactly the corresponding theorem's conclusion, with its full
source parameter and instance telescope. This focused pair makes the following
changes:

- Prefix `LocalFieldTheory` by `Langlands.NYLL` and append `Statement` to the
  two theorem names.
- Replace each `theorem ... : conclusion := by ...` by
  `def ... : Prop := conclusion`. The proof bodies at source lines 37–59 and
  66–77 are omitted. No theorem proof or additional assumption is introduced.
- Replace the full original NYLL Basic import at line 7 with the published
  `UnitTopology.U001.Definitions` import. That module imports the published
  `Basic.U016.Definitions`, which provides the original inclusion map and
  imports `Mathlib.NumberTheory.LocalField.Basic`. These supply the subgroup,
  canonical valuation, local-field class and topology used in the targets.
- Reuse the published subgroup from source lines 28–31 without copying its
  definition. Remove the source's `open
  _root_.LocalFieldTheory.IsNonarchimedeanLocalField`, whose short inclusion-map
  name is used only in the subgroup definition and omitted proof. Retain the
  source's `noncomputable section`, universe and scoped `ValuativeRel` opening.
- Focus the module prose and docstrings on proposition targets. Preserve the
  original copyright and author header and add the dated modification notice.

The related host `Langlands.PadicField.TopologicalData.unitSubgroup` uses
supplied p-adic field data. These targets retain the source's arbitrary
`Field`/`ValuativeRel` interface and the actual published NYLL image subgroup.
No new instances are declared. The M128 normalized integer valuation is not
needed to state these targets.

Focused Lake compilation with only the displayed direct import succeeds.
Private declaration inspections
`81f41e98-f873-45b1-9fc0-90ec5ced9644` and
`24b0cd20-aa93-4233-993a-b1fce6548d24` confirm that the first and second
definitions, respectively, retain universe `u` and return `Prop`; both checks
report zero errors and warnings. These development checks establish neither
proposition.

## Attribution and status

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original author is Naganori Yamaguchi, assisted by OpenAI Codex. Worker 94
prepared this extraction on 12 November 2026. The retained Apache-2.0 files are
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
No UnitTopology-specific NOTICE entry or patch10 change applies.

The two exact proofs remain separate work after target publication. These
support statements do not establish any host class-formation, cup, transfer,
Tate or reciprocity target.
