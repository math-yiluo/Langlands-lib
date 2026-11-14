<!-- MANUAL -->
# Packaged local fields of arbitrary characteristic

Lean module: `Langlands.AllFieldBZ.LocalField.Definitions`. It is the foundation of the all-field
port. It replaces the p-adic foundation modules `Langlands.LocalField.{Definitions, Canonical,
Topology, Normalization.Definitions, Normalization.Statement, Normalization.Proof, Uniformizer}`,
which are written for `Langlands.PadicField p`, a finite extension of `ℚ_p`.

## Definitions

- `Langlands.AllFieldBZ.LocalFieldPackage` (structure, universe `u`): a carrier type
  `Carrier : Type u` with a `Field` instance `field`, registered with `attribute [instance]`.
  It has no characteristic hypothesis and no base field. It takes the role of
  `Langlands.PadicField p` with the `Algebra (Padic p)` and finite-dimensionality fields removed,
  so it can package a nonarchimedean local field of positive characteristic such as `𝔽_q((t))`.
- `Langlands.AllFieldBZ.LocalFieldPackage.ofField K` packages a field `K` with its given `Field`
  instance; its `Carrier` is `K` by definition.
- `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData F` (an `abbrev`) is the Library structure
  `Langlands.LocalFieldData F.Carrier`. That structure consists of a topology, a `ValuativeRel`, and
  an `IsNonarchimedeanLocalField` certificate. The normalization API (`Integers`, `ResidueField`,
  `residueCardinality`, `uniformizer`, `discreteValuation`, `ord`, `normalizedAbs`, and their
  laws) is the Library API of `LocalFieldData` (modules `Langlands.LocalField.LocalFieldData` and
  `Langlands.LocalField.LocalFieldArithmetic`).

These three declarations keep the names and bodies of the stand-in from Worker 5677's draft
revision 2, which the exact-target bridge
`Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyBridge` uses.

## Lemmas

In namespace `Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData`, for
`F : LocalFieldPackage` and `T : F.TopologicalData`:

- `fieldT2`: the topology `T.topology` is Hausdorff. Proof: the Library instance
  `Langlands.HarmonicAnalysis.GeneralLocalField.t2Space`.
- `infinite` (`T` explicit): `F.Carrier` is infinite. Proof: `n ↦ ϖ ^ n`, for the uniformizer `ϖ`
  of `T`, is injective, since `ord (ϖ ^ n) = n` (Library lemmas `LocalFieldData.ord_zpow` and
  `LocalFieldData.ord_uniformizer`).
- `normalizedAbs_eq_zero_iff x`: `T.normalizedAbs x = 0 ↔ x = 0`. Proof: positivity off zero
  (`LocalFieldData.normalizedAbs_pos`) and `LocalFieldData.normalizedAbs_zero`. The ported
  `RankinSelberg.AnalyticStatement` uses it.
- `normalizedAbs_le_one_iff_mem_integers x`: `T.normalizedAbs x ≤ 1 ↔ x ∈ T.Integers`. Proof:
  for `x ≠ 0`, compare the discrete valuations of `x` and `1`
  (`LocalFieldData.normalizedAbs_le_iff_of_ne_zero`), then use that the order isomorphism
  `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` is strictly monotone.
- `residueNormalizedAbsoluteValue_eq_normalizedAbs x`: the Library's residue-normalized absolute
  value `LocalField.residueNormalizedAbsoluteValue F.Carrier x` equals `T.normalizedAbs x`. Proof:
  both are `0` at `0`; for `x ≠ 0` both are `q ^ (-ord x)`, where `q` is the residue cardinality.
- `continuous_normalizedAbs`: `T.normalizedAbs` is continuous for `T.topology`. Proof: the previous
  lemma and the Library theorem `Plancherel.continuous_residueNormalizedAbsoluteValue`.
- `exists_normalizedAbs_lt_subset hU`: for every neighbourhood `U` of `0`, there is `ε > 0` such
  that `T.normalizedAbs x < ε` implies `x ∈ U`. Proof: the valuative neighbourhood basis
  (`IsValuativeTopology.hasBasis_nhds_zero'`) gives `γ ≠ 0` with `{x | v x < γ} ⊆ U`. Take `ε` to be
  the normalized absolute value of a preimage `x₀` of `γ`. Then `|x| < |x₀|` implies
  `v x < v x₀ = γ`.

## Provenance

These are internal interface definitions and elementary facts about nonarchimedean local fields,
with no literature counterpart. Written by Worker 71. Worker 5677 wrote the first version of the
three definitions as a stand-in.
