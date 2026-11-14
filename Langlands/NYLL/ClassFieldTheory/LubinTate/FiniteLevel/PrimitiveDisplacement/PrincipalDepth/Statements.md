# Exact principal-unit depth: statements (NYLL M362.022 and M362.026)

This module defines two Prop-valued statement targets,
`Langlands.NYLL.PortInternal.M362.d022Statement.{u, v}` and
`Langlands.NYLL.PortInternal.M362.d026Statement.{u, v}`.
They are the propositions of the source-private NYLL units M362.022 and
M362.026 in
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file SHA-256 is
`520ab08231608ac43915d72c8a94c5d4ea1ad2fd4b7311a77f8f889a37421cbc`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

## Shared parameters

Source lines 33–43 declare universes `u v`, enter namespace `LubinTate`,
open `LocalFieldTheory.DiscreteValuationField` and three further
namespaces, and fix the implicit parameters
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring}`.
Both targets keep these four implicit parameters in that order, with the
field universe `u` and the value-group universe `v` independent.
`LocalField` is the published shared package
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`, and
level `n` of the filtration is the published concrete subgroup
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF n`
of `F.valuationSubringˣ`, whose carrier is the set of units `u` with
`u - 1 ∈ F.maximalIdeal ^ n` (NYLL M225.001).

## M362.022: `d022Statement`

Source: private theorem
`LubinTate.exists_unit_mul_uniformizer_pow_of_exactDepth`, lines 405–446
(binders and conclusion at lines 405–414).

The explicit arguments, in source order, are a proof
`_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, a unit
`a : F.valuationSubringˣ`, a natural number `k`, a proof `_ha` that `a`
lies in level `k`, and a proof `_hnot` that `a` does not lie in level
`k + 1`. The proposition is

`∃ c : F.valuationSubringˣ, (a : F.valuationSubring) - 1 = (c : F.valuationSubring) * π ^ k`,

so an element of the exact `k`-th principal-unit layer differs from one by a
valuation-ring unit times `π ^ k`.

## M362.026: `d026Statement`

Source: private theorem
`LubinTate.mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow`,
lines 574–610 (binders and conclusion at lines 574–582).

The explicit arguments, in source order, are a proof
`_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, units
`a c : F.valuationSubringˣ`, natural numbers `r k`, and a proof
`_hsub : (a : F.valuationSubring) - 1 = (c : F.valuationSubring) * π ^ r`.
The proposition is

`a ∈ higherPrincipalUnitGroup F.toCompleteDVF k ↔ k ≤ r`,

so when `a - 1` is a specified unit times `π ^ r`, membership of `a` in
level `k` holds exactly for `k ≤ r`.

## Modifications from the source

- Extraction of the two theorem statements only; their tactic proofs are
  not included.
- Each theorem is replaced by a Prop-valued `def` whose value is the
  source conclusion. The source hypotheses remain explicit arguments, in
  their original order and with their original types, even though the
  propositions do not depend on their values; their binder names gain a
  leading underscore (`_hπ`, `_ha`, `_hnot`, `_hsub`).
- The source-private names are replaced by the port's reserved
  implementation names with a `Statement` suffix:
  `exists_unit_mul_uniformizer_pow_of_exactDepth` ↦
  `PortInternal.M362.d022Statement`, and
  `mem_higherPrincipalUnitGroup_iff_le_of_sub_eq_unit_mul_uniformizer_pow` ↦
  `PortInternal.M362.d026Statement`. The source namespace `LubinTate` is
  replaced by `Langlands.NYLL.PortInternal.M362`.
- The opened namespace is qualified as
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`; the conclusions
  write `CompleteDVF.higherPrincipalUnitGroup` as in the source. The unused
  source opens (`LocalFieldTheory.DiscreteValuationField.CompleteDVF`,
  `RamificationTheory.HilbertRamification.Higher`,
  `ValuationTheory.DiscreteValuationField`, and the `Polynomial` and
  `PowerSeries` scoped notations of line 31) are omitted.
- The source imports (completed iterates, primitive action, level valuation
  and power-series inverses) are replaced by the two published modules the
  statements use:
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`
  and
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`.
  Neither statement uses level-field, primitive-action or formal-module data.
- The module documentation is replaced by a one-line title. No instances
  are added.

No hypothesis, binder type or conclusion has otherwise changed.
The Lean header retains the original copyright, authorship and Apache-2.0
notice and records the modification; the Library carries
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Scope and use

This module states two propositions and proves neither; their exact proofs
are routed separately after these targets are published. In the source,
M362.023 (line 450) applies M362.022 to show that the standard Lubin–Tate
endomorphism value at `a - 1` has additive valuation `q ^ k` at level `n`,
where `q` is the residue-field cardinality, when `a` has exact depth
`k ≤ n`. M362.027 (line 615) and later units apply M362.026 to detect
principal-unit levels by the valuation of a displacement.

The pair originates in Worker 299's shared draft revision 1 for this task;
Worker 469 rechecked it against the source, added the module title and
expanded this description.
