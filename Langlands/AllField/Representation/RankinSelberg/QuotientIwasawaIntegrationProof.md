# All-field port of `Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof`

`Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized quotient Iwasawa integration**

The compact-open orbit formula and diagonal conjugation compute the restriction
of any compatible quotient measure to each uniformizer orbit. The published
torus-sum identity identifies the sum of these restrictions with the normalized
inverse-modulus-weighted torus/compact pushforward.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusSumProof`
- `Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.quotientIwasawaIntegration` (theorem): Every compatible left-unipotent quotient measure is the normalized
  inverse-modulus-weighted pushforward of diagonal Haar and restricted compact Haar.
