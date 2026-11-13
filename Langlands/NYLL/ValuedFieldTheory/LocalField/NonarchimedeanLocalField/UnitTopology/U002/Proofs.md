# Valuation characterization of the valuation-integer unit subgroup

This module proves the published proposition
`Langlands.NYLL.LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_oneStatement`.
The theorem's complete interface is:

```lean
theorem Langlands.NYLL.LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_one
    (K : Type u) [Field K] [ValuativeRel K] (x : Kˣ) :
    Langlands.NYLL.LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_oneStatement K x
```

Thus `x` lies in the actual image of the canonical valuation-ring unit map
exactly when `ValuativeRel.valuation K (x : K) = 1`. The universe `u`, explicit
`K`, instance order, and explicit `x` agree with the source and published target.
There is no topology or local-field premise.

## Implemented proof

After exposing the target's proposition body, the forward implication
eliminates membership in the range as `⟨a, rfl⟩`. Mathlib's
`Valuation.Integers.valuation_unit`, applied to
`Valuation.integer.integers (ValuativeRel.valuation K)`, says that the image of
the valuation-ring unit `a` has valuation one. Simplification unfolds the
published inclusion map.

For the reverse implication, let the valuation of `x` be one. Construct a unit
of `𝒪[K]` with value `x` and inverse `x⁻¹`. The criterion
`Valuation.mem_integer_iff` reduces both valuation-ring membership obligations
to valuation at most one. The given equality handles `x`; simplification of
the valuation of the inverse handles `x⁻¹`. The two unit laws follow from
`mul_inv_cancel₀ x.ne_zero` and `inv_mul_cancel₀ x.ne_zero` after subtype
extensionality. This unit maps to `x` by units extensionality and reflexivity,
giving the required range witness.

## Source correspondence and changes

This is M256.002, Naganori Yamaguchi's
`LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_one`, at lines
33–59 (declaration at 35–37) of
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean>)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The original file SHA-256
is `77d63306c40bd28166878221e43427bbbcd699daeee497bbe40c82935d928f43`.
Worker 233 read the complete original UnitTopology file and the published
statement, subgroup and inclusion-map definitions.

The proof follows the original proof body. The modifications are:

- Prefix the source namespace and opened inclusion-map namespace by
  `Langlands.NYLL`.
- Give the theorem the exact published named proposition as its result type
  and add a `change` to expose its unchanged proposition body.
- Replace the original full NYLL Basic import with the single direct import
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.Statements`.
- Retain only M256.002, focus the module prose, and add the dated modification
  notice. The published target and its imported files are unchanged.

The actual import chain is `UnitTopology.Statements` →
`UnitTopology.U001.Definitions` → `Basic.U016.Definitions` →
`Mathlib.NumberTheory.LocalField.Basic`. It supplies the canonical inclusion
map, its image subgroup, the valuation-ring constructions and all proof tools.
No additional import, helper theorem or instance is introduced. The other
UnitTopology theorem and M128 normalized integer valuation data are not needed.

## Development validation

The focused Lean-service check
`204bb441-c0fb-4e16-bc0d-83d15a2b4046` compiled this module with zero errors and
warnings. Lake build and declaration inspection
`560df232-e73a-45bb-bd30-e97cacbb5fae` also succeeded with zero errors and
warnings, reported the theorem's sole universe parameter `u`, and found only
`propext`, `Classical.choice` and `Quot.sound` as axioms. These checks used
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`; they are development evidence,
separate from independent review and formal exact-target validation.

## Attribution and scope

The original author is Naganori Yamaguchi, assisted by OpenAI Codex. The source
registration is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Worker 233 prepared this focused adaptation on 13 November 2026.

The original copyright and author header is preserved. The retained
Apache-2.0 files are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
No UnitTopology-specific NOTICE entry or patch10 change applies.

This support proof characterizes the published unit subgroup. It establishes
no host class-formation or reciprocity result.
