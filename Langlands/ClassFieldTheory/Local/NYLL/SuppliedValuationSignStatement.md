# Valuation sign compatibility for supplied local-field data

The module defines the proposition
`Langlands.LocalClassField.NYLL.SuppliedValuationSignStatement.{u}`.
It quantifies over every natural number `p` with `[Fact p.Prime]`, every
`F : Langlands.PadicField.{u} p`, arbitrary supplied
`T : F.TopologicalData`, and every unit `a : F.Carrierˣ`.
The coefficient-field universe `u` is arbitrary.

For those data the proposition installs exactly `T.topology`,
`T.valuativeRel`, and `T.localField` as local instances, in that order, and
states

```lean
Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
  F.Carrier (Additive.ofMul a) = -T.ord (a : F.Carrier)
```

The field operations are those already attached to `F.Carrier`. Both sides
use the supplied data `T`; no canonical replacement or additional comparison
certificate is assumed. The unit supplies nonzeroness, so the statement
needs no separate nonzero or uniformizer premise. It installs no global
instance.

## Construction and sign

The module imports the published definition pairs
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`
and `Langlands.LocalField.Normalization.Definitions` without modifying them.
The relevant constructions are:

- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`
  is `MonoidHom.toAdditive` of `valuationUnitsMulHom`. That multiplicative
  homomorphism applies `Units.map` of the actual `ValuativeRel.valuation`,
  then `Units.map` of Mathlib's
  `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`, then
  `WithZero.unitsWithZeroEquiv`. It extracts the integer exponent of a
  nonzero multiplicative value without inserting a negation.
- `Langlands.PadicField.TopologicalData.discreteValuation` composes the
  same actual valuation with the same ordered value-group isomorphism,
  using the same supplied topology, valuative relation, and local-field
  instances.
- `Langlands.PadicField.TopologicalData.ord` is defined by
  `T.ord x = -WithZero.log (T.discreteValuation x)`.

Thus the sign comparison to be proved is with **negative** `T.ord`:
negating the host order removes the negation in its definition and matches
the exponent extracted by the NYLL map. `Additive.ofMul` only changes the
type tag on the unit input. The host order has a convention at zero, but
this proposition only evaluates it on units.

## Provenance and scope

This is an internal derived compatibility target between the two actual
published constructions above. It is not a translation of a separate
original-literature theorem. The imported NYLL definition pair records the
upstream source, license, attribution, and extraction history; the host
normalization pair records its own provenance. This module imports those
definitions by Lean name and reuses no original source text or implementation
body.

The proposition definition contains no proof of the equality. Neither
definition module already proves this comparison, and neither the source
function `v` nor `valuationMap_apply` is required to state it. An exact proof
of this published proposition is a separate obligation. This focused
statement makes no Artin-map, extension, unramified, residue, or generic
valuation-law assertion.

Worker 109 specified the exact interface and sign in the task contract.
Worker 542 authored this Lean statement and its paired explanation.
The imported definitions retain their original authorship. The environment
is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
