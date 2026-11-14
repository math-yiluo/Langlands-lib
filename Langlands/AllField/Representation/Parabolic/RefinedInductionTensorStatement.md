# All-field port of `Langlands.Representation.Parabolic.RefinedInductionTensorStatement`

`Langlands.AllField.Representation.Parabolic.RefinedInductionTensorStatement` is the all-field port of the Library module `Langlands.Representation.Parabolic.RefinedInductionTensorStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinedInductionTensorStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Tensor compatibility for normalized induction in an actual product Levi.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement`
- `Langlands.AllField.Representation.Induction.Parabolic`

## Declarations

- `Langlands.AllField.Parabolic.RefinedInductionTensor.Factors` (abbrev): Smooth representations of the actual inner Levi factors.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.inducingRepresentation` (def): The external tensor action transported to the actual refined subgroup.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.BlockFunctions` (abbrev): The actual function carrier for one block's normalized induction.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.blockRepresentations` (def): The family of actual normalized induced block actions.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.externalRepresentation` (def): The actual external tensor of the normalized induced block actions.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.RefinedFunctions` (abbrev): The actual tensor-valued function carrier for refined normalized induction.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.refinedRepresentation` (def): Actual normalized induction of the transported external tensor action.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.CanonicalInverse` (def): The canonical inverse sends a pure tensor of induced functions to its
  pointwise tensor-valued product function.
- `Langlands.AllField.Parabolic.RefinedInductionTensor.Comparison` (def): Existence of an actual equivalence with its canonical inverse prescribed.
- `Langlands.AllField.Parabolic.RefinedInductionTensorTheorem` (def): Normalized induction in every actual product Levi commutes with the finite
  external tensor product, with the pointwise pure-tensor inverse prescribed.
  The field and coefficient universes are independent. This is a statement.
