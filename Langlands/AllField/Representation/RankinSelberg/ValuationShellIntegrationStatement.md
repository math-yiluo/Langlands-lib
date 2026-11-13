# All-field port of `Langlands.Representation.RankinSelberg.ValuationShellIntegrationStatement`

`Langlands.AllField.Representation.RankinSelberg.ValuationShellIntegrationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.ValuationShellIntegrationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.ValuationShellIntegrationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Valuation-shell decomposition of normalized multiplicative Haar integrals**

A derived interface for the valuation-shell route to the one-variable Mellin
argument of JPSS (1983), printed page 392. The unit group of a nonarchimedean local
field, with supplied data `T : LocalFieldData F`, is the disjoint union of the shells
of fixed normalized order, each a translate of the integral units by a power of a
uniformizer. The actual multiplicative
Haar integral of a continuous complex function is the sum of its shell
integrals. No part of the decomposition is proved here.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.RankinSelberg.ValuationShellIntegrationStatement` (def): Shell geometry, local integrability, the integrability criterion and the
  integral identity for the actual normalized multiplicative Haar measure.
  The measure, the integral units and the shells are local to this proposition;
  the uniformizer is an existential witness.
