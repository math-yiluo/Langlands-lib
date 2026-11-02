# The p-adic and Laurent-series fields as instances of one consumer

Worker 785 instantiates the common consumer `Langlands.LocalField.NormalizedAt`
of `Langlands.LocalField.NormalizationConsumer` by the actual X-adic
Laurent-series field of `Langlands.LocalField.LaurentSeries` (Worker 27), and
records that this field and every p-adic field feed the same consumer. This is a
narrow compiled adapter: no new field family, bundled representation category,
topology, valuation or normalization is introduced.

## Laurent-series instantiation

For `k : Type u` with `[Field k] [Finite k]`, the module installs only locally
the published explicit valuative relation
`Langlands.LocalField.Laurent.valuativeRel k`, which is
`ValuativeRel.ofValuation` of Mathlib's X-adic valuation `Valued.v`. The topology
is Mathlib's existing one on `LaurentSeries k`, coming from its valued uniform
structure, and `IsNonarchimedeanLocalField (LaurentSeries k)` is the published
instance `Langlands.LocalField.Laurent.localField`. Nothing about the field
structure is assumed.

- `Langlands.LocalField.Laurent.normalizedAt` proves
  `NormalizedAt (LaurentSeries k) (Nat.card k)`. It applies the general
  `normalizedAt_iff` to the published `residueCardinality_eq`, which computes the
  cardinality of the actual residue field of the actual valuation ring through
  the ring equivalence `residueEquiv` with `k` itself.
- `Langlands.LocalField.Laurent.residueNormalizedAbsoluteValue_zpow_of_ord_one`
  is the resulting evaluation: if `Langlands.FML.ord (LaurentSeries k) π = 1`,
  then `residueNormalizedAbsoluteValue (LaurentSeries k) (π ^ n)` equals
  `(Nat.card k : ℝ) ^ (-n)` for every integer `n`, including negative `n`.

The order is the published `FML.ord`, with `ord 0 = ⊤`; the absolute value is
the published `residueNormalizedAbsoluteValue`. Thus order one has absolute
value `(Nat.card k)⁻¹`. Evaluation at the particular series `X` needs the order
computation `FML.ord (LaurentSeries k) X = 1`. That computation is the published
`Langlands.LocalField.Laurent.ord_X` of Worker 27's
`Langlands.LocalField.LaurentNormalization`, which also evaluates the absolute
value at `X` and its integer powers directly. This module does not import it
and proves no order calculation of its own.

## Common consumer for both families

`Langlands.LocalField.PadicLaurentNormalized.{u, v}` is the proposition that for
every prime `p`, every `F : Langlands.PadicField.{u} p` and every finite field
`k : Type v`:

- with the topology, valuative relation and local-field instance of the
  published `F.canonicalTopologicalData`, `NormalizedAt F.Carrier
  F.canonicalTopologicalData.residueCardinality` holds; and
- with `Laurent.valuativeRel k`, `NormalizedAt (LaurentSeries k) (Nat.card k)`
  holds.

`padicLaurentNormalized` proves it by pairing the published p-adic
`Langlands.PadicField.canonical_normalizedAt` with `Laurent.normalizedAt`. The two
families remain separate types with their own published constructions; they
meet only through the general `IsNonarchimedeanLocalField`-based predicate.

## Provenance and limits

This is an internal derived adapter. It imports by module name Worker 27's
`Langlands.LocalField.LaurentSeries`, Worker 785's
`Langlands.LocalField.NormalizationConsumer`, and through them Worker 607's
`ResidueNormalization` and `PadicResidueNormalization` and the published
`Langlands.LocalField.Canonical`. It copies no source. The normalization
`|π| = q⁻¹` is that of `ResidueNormalization`, whose Markdown records its source.
The predicates here are Lean-specific packaging rather than numbered source
theorems. Nothing here classifies local fields or constructs a building or
parahoric model.
