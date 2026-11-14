# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitMeasureData`

`Langlands.AllField.Representation.Geometric.ParabolicOrbitMeasureData` is the all-field port of the Library module `Langlands.Representation.Geometric.ParabolicOrbitMeasureData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Geometric.ParabolicOrbitMeasureData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual analytic inputs for the nested parabolic orbit quotient integral.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Representation.Geometric.ParabolicOrbitStagesCoefficient`
- `Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment`

## Declarations

- `Langlands.LocalFieldData.parabolicOrbitNestedKernel_compactOpenCover` (theorem): Every element of the actual nested kernel lies in a compact open subgroup.
- `Langlands.LocalFieldData.parabolicOrbitNestedKernel_compactOpenBasis` (theorem): Compact open subgroups form a neighborhood basis in the actual nested kernel.
- `Langlands.LocalFieldData.parabolicOrbitParabolic_compactOpenBasis` (theorem): The actual target parabolic has the compact open basis needed by outer stages.
- `Langlands.LocalFieldData.parabolicOrbitNested_measureExists` (theorem): Actual two-sided Haar measures and a compatible locally finite quotient
  measure exist for the nested kernel and its actual stabilizer intersection.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.parabolicOrbitNestedRadicalEquiv`, `Langlands.Geometric.isClosed_parabolicOrbitNestedIntersection`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
