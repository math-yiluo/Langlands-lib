# A common consumer of the residue-normalized local-field API

Worker 785 provides a narrow consumer of the published general normalization in
`Langlands.LocalField.ResidueNormalization`. It is stated once for an arbitrary
`F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, and is then instantiated by every supplied
p-adic realization. A separate adapter instantiates it by the actual X-adic
Laurent-series field of `Langlands.LocalField.LaurentSeries`. No new field
family, representation category, normalization convention or global instance is
introduced.

## The consumer

`Langlands.LocalField.NormalizedAt F q` is the proposition that

- the actual residue cardinality `residueCardinality F` equals `q`;
- `1 < q`; and
- for every `π : F` with `Langlands.FML.ord F π = 1` and every integer `n`,
  `residueNormalizedAbsoluteValue F (π ^ n) = (q : ℝ) ^ (-n)`.

Here `π ^ n` is the integer power in the field `F` (so `n < 0` uses inverses),
`FML.ord` is the existing additive order with `ord 0 = ⊤`, and
`residueNormalizedAbsoluteValue` is the existing bundled absolute value. The
sign convention is therefore the source-standard one already fixed by the
general construction: an element of order one has absolute value `q⁻¹`, and
negative powers have absolute value greater than one. No competing order or
absolute-value normalization is defined.

## General results

- `residueNormalizedAbsoluteValue_zpow_of_ord_one` proves the integer-power
  formula with `q = residueCardinality F`. The proof rewrites with Mathlib's
  `map_zpow₀` (an absolute value into `ℝ` is a monoid-with-zero homomorphism),
  the published `residueNormalizedAbsoluteValue_of_ord_one`, and `inv_zpow'`.
- `normalizedAt_residueCardinality` proves `NormalizedAt F (residueCardinality F)`;
  the bound `1 < q` is the published `residueCardinality_gt_one`.
- `normalizedAt_iff` records that `NormalizedAt F q` holds exactly when
  `residueCardinality F = q`. Thus an instantiation of the consumer is the same
  information as an identification of the actual residue cardinality.
- `NormalizedAt.residueNormalizedAbsoluteValue_uniformizer` evaluates the
  published chosen `uniformizer F` to `(q : ℝ)⁻¹`.

## p-adic instantiation

For a prime `p`, `F : Langlands.PadicField.{u} p` and a supplied
`T : F.TopologicalData`, `Langlands.PadicField.TopologicalData.normalizedAt`
installs exactly `T.topology`, `T.valuativeRel` and `T.localField` locally and
proves `NormalizedAt F.Carrier T.residueCardinality`, using the host residue
cardinality. It rewrites with the published
`general_residueCardinality_eq` of `Langlands.LocalField.PadicResidueNormalization`.
`normalizedAbs_zpow_of_ord_one` transfers the integer-power formula to the
existing host absolute value `T.normalizedAbs` through the published pointwise
bridge `residueNormalizedAbsoluteValue_eq_normalizedAbs`.

`Langlands.PadicField.canonical_normalizedAt` specializes to the published
`F.canonicalTopologicalData` of `Langlands.LocalField.Canonical`, so every
`PadicField` with its canonical spectral-norm topology and valuation is a
consumer instance. The p-adic field constructor, canonical topology and
compatibility proofs are imported, not rebuilt.

## Provenance and limits

This is an internal derived adapter. Its content is assembled from the published
Lean constructions `Langlands.LocalField.ResidueNormalization` and
`Langlands.LocalField.PadicResidueNormalization` (authored by Worker 607), and
`Langlands.LocalField.Canonical`, imported by module name without copying source.
The normalization `|π| = q⁻¹` is the convention of those modules; their Markdown
records its source (Renard, *Représentations des groupes réductifs p-adiques*,
V.1). The predicate `NormalizedAt` is a Lean-specific packaging for consumers
and is not a separately numbered theorem in that source. Nothing here classifies
local fields, uses Haar measure, or depends on the residue characteristic.
