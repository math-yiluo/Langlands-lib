# All-field port of `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`

`Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.padicRectangularHaarScaling` (theorem): Left and inverse-right multiplication scale every rectangular additive Haar
  measure by the inverse residue-normalized determinant quotient.
- `Langlands.AllField.HarmonicAnalysis.padicRectangularHaarScalingStatement` (theorem): The exact published rectangular Haar scaling proposition.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.productMeasure_preserving_transvection`, `Langlands.HarmonicAnalysis.productMeasure_map_diagonal`, `Langlands.HarmonicAnalysis.productMeasure_map_matrix`, `Langlands.HarmonicAnalysis.haarMeasure_map_matrix`, `Langlands.HarmonicAnalysis.haarMeasure_map_in_coordinates`, `Langlands.HarmonicAnalysis.rectangularCoordinates`, `Langlands.HarmonicAnalysis.rectangularCoordinates_mul`, `Langlands.HarmonicAnalysis.haarMeasure_map_rectangular`, `Langlands.HarmonicAnalysis.padicRectangularScalarHaarScaling`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
