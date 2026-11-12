# Continuity of the valuation-integer unit inclusion

Worker 202 supplies the exact proof increment M255.003 for the published
proposition
`Langlands.NYLL.LocalFieldTheory.integerUnitsToFieldUnits_continuousStatement`.
The source theorem name is retained under `Langlands.NYLL.LocalFieldTheory`,
with the complete interface

```lean
theorem integerUnitsToFieldUnits_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    integerUnitsToFieldUnits_continuousStatement K
```

The universe `u`, explicit `K`, instance order and all hypotheses are unchanged.
The target unfolds to continuity of the actual published homomorphism
`IsNonarchimedeanLocalField.integerUnitsToFieldUnits K : 𝒪[K]ˣ →* Kˣ`.
The valuation-integer ring carries its subtype topology and both unit groups
carry Mathlib's canonical unit topology. The topology on `K` is arbitrary;
no compatibility with the valuation or continuity of field operations is
assumed.

## Implemented proof and dependencies

The sole direct import is the published target module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.U003.Statements`.
It imports the published map definition from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`
and `Mathlib.Topology.Algebra.Group.Units`.

The proof exposes `Continuous (integerUnitsToFieldUnits K)` with `change`
and unfolds the map to
`Units.map (algebraMap 𝒪[K] K).toMonoidHom`. The underlying algebra map is
the subtype inclusion, whose continuity is `continuous_subtype_val`.
Mathlib's `Continuous.units_map` then gives the required continuity.
That lemma, in `Mathlib.Topology.Algebra.Monoid`, applies
`Units.continuous_iff` to the value and inverse-value coordinates, composing
the given continuous map with `Units.continuous_val` and
`Units.continuous_coe_inv`. It needs only monoids and topological spaces.
Thus this proof uses the native unit topology without adding assumptions
on multiplication or inversion in the field.

The other norm-continuity units M255.001 and M255.002 are not dependencies.
The published target, map definition and their imports are unchanged.

## Source correspondence and attribution

The original is Naganori Yamaguchi's ClassFieldTheory, assisted by OpenAI
Codex, at commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean`,
lines 60–67, unit M255.003,
`LocalFieldTheory.integerUnitsToFieldUnits_continuous`.
The source file SHA-256 is
`8cd7c49384a442469cff5bf0397150f52b24b03fa3087b3b252b29e9e05b38a8`.
The pinned source is retained under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project errata notes.

Worker 202 preserves the source proof route, parameters and universe, prefixes
the namespace, replaces the source conclusion with its already published
proposition and adds `change` to expose that proposition. The original full
NYLL and analytic imports are replaced by the focused target import above.
The unused source universe `v` and noncomputable section are omitted.
No patch10 compatibility code is incorporated.

The original copyright and author header is preserved verbatim, with an
explicit modification notice. The unchanged Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain at `licenses/NYLL/`.
Their SHA-256 values, verified against the pinned source, are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no source-specific entry for this file.
