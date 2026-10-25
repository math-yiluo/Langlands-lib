# Relative valuation compatibility for supplied local-field data

Worker 104 authored the Lean definition and this explanation. Worker 66
specified the interface and its role in the NYLL norm/transfer bridge.

The module `Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationStatement`
defines the proposition
`Langlands.LocalClassField.NYLL.SuppliedRelativeValuationExtensionStatement.{u,v}`.
The field universes `u` and `v` are independent. The proposition quantifies over
every `p : ℕ`, a certificate `[Fact p.Prime]`, fields
`F : PadicField.{u} p` and `E : PadicField.{v} p`, an actual
`[Algebra F.Carrier E.Carrier]`, its compatibility certificate
`[IsScalarTower (Padic p) F.Carrier E.Carrier]`, and arbitrary supplied
`TF : F.TopologicalData` and `TE : E.TopologicalData`.

Inside that quantification it installs exactly `TF.valuativeRel` and
`TE.valuativeRel` as local instances, in that order. Its conclusion is

```lean
Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
  (ValuativeRel.valuation E.Carrier)
```

Writing `vF` and `vE` for these two valuations, Mathlib defines this class by
the condition `vF.IsEquiv (vE.comap (algebraMap F.Carrier E.Carrier))`.
Thus the statement concerns extension along the given relative field map.
Equivalence compares valuation order relations; it does not require numerical
equality in independently normalized value groups.

This is an internal, derived compatibility obligation. Its immediate inputs
and provenance are the published `Langlands.LocalField.RelativeIntegers` and
the pinned Mathlib valuation definitions:

- `Langlands.PadicField.TopologicalData.Integers` in
  `Langlands.LocalField.Normalization.Definitions` is the integer ring of
  `ValuativeRel.valuation` with precisely the supplied valuative relation.
- `Langlands.PadicField.TopologicalData.relative_mem_integers_iff TF TE x`
  compares membership of `algebraMap F.Carrier E.Carrier x` in `TE.Integers`
  with membership of `x` in `TF.Integers`, for these same quantifiers. Its
  published proof uses the supplied-data canonical-norm comparison and the
  canonical norm's compatibility with the actual field map.
- `Valuation.HasExtension` in
  `Mathlib.RingTheory.Valuation.Extension` packages equivalence with the
  valuation comap. `Valuation.isEquiv_iff_val_le_one` in
  `Mathlib.RingTheory.Valuation.Basic` characterizes this equivalence by the
  two valuations' elements of value at most one.

These existing interfaces identify the remaining proof obligation: express
the integer-membership equivalence as the value-at-most-one equivalence,
orient it from the base valuation to the comap, and package it in
`Valuation.HasExtension`. This module imports the existing comparison and
states that obligation; it contains no proof of it. It makes no additional
claim of correspondence with an original literature theorem.

The fields' existing `PadicField` structures supply their finite-dimensional
extensions of `Padic p`. The statement assumes no relative valuation-extension
certificate, Galoisness, abelianity, or extra arithmetic result. The supplied
data remain arbitrary; no canonical realization is substituted. Neither
topological nor uniform structures are installed locally, and no global
instance, integer or residue map, or new data constructor is introduced.

The intended use is the supplied-data extension-instance obligation discussed
in [NYLL port feasibility, section 6](../../../../notes/reuse/nyll-port-feasibility.md)
and [the NYLL audit, sections 2.4 and 5](../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md).
The namespace identifies this host-facing interface, but the module imports no
external NYLL port. Defining this proposition proves neither the bridge nor
any reciprocity, norm/transfer, class-formation, or cup-product theorem.

The reused Library and Mathlib declarations retain their original authorship.
The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
