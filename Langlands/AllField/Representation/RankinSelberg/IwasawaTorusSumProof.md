# All-field port of `Langlands.Representation.RankinSelberg.IwasawaTorusSumProof`

`Langlands.AllField.Representation.RankinSelberg.IwasawaTorusSumProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.IwasawaTorusSumProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.IwasawaTorusSumProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Discrete torus decomposition of the normalized Iwasawa pushforward**

The published uniformizer-coset partition reduces the weighted torus integral to
a countable sum. The modulus is constant on each coset, and left invariance of
restricted compact Haar absorbs its integral diagonal unit factor.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusSumStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.iwasawaTorusSum` (theorem): The normalized torus/compact pushforward is the inverse-modulus-weighted sum
  of compact pushforwards at every uniformizer exponent vector.
