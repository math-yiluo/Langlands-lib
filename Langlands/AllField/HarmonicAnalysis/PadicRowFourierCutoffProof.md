# All-field port of `Langlands.HarmonicAnalysis.PadicRowFourierCutoffProof`

`Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicRowFourierCutoffProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicRowFourierCutoffProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Simultaneous normalized local-field row Fourier cutoffs: proof**

A compact open product subgroup `L = Sᵈ` of rows lies inside the prescribed
neighbourhood of zero, and the character of the row pairing is trivial on
`L × C`. The small cutoff is `κ = vol(L)⁻¹ · 1_L`, and the large cutoff is its
plus-sign row transform. Row inversion and the evenness of `κ` make the pair
`(Φ, κ)` a Fourier pair in the stated direction.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffStatement`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.padicRowFourierCutoff` (theorem): Simultaneous normalized row Fourier cutoffs for every supplied topology,
  self-dual scalar Haar measure and dimension.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.exists_rowCutoffSubgroup`, `Langlands.HarmonicAnalysis.exists_rowFourierCutoff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
