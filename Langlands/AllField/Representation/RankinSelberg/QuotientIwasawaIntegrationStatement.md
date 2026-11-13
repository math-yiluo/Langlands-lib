# All-field port of `Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement`

`Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized quotient Iwasawa integration**

This proposition states the measure identity underlying JPSS Theorem 2.7,
printed p391, equation (3). It uses ordinary diagonal entries and the published
mass-one Haar normalizations. It does not prove the integration formula.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.RankinSelberg.QuotientIwasawaIntegrationStatement` (def): Every compatible measure on the actual left-unipotent quotient is the
  pushforward of diagonal Haar times the restricted compact Haar, weighted by
  the inverse upper-Borel modulus. No integrability hypothesis is imposed.
