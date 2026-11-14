# All-field port of `Langlands.Representation.Parabolic.RegroupingFactorEquivalences`

`Langlands.AllField.Representation.Parabolic.RegroupingFactorEquivalences` is the all-field port of the Library module `Langlands.Representation.Parabolic.RegroupingFactorEquivalences`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RegroupingFactorEquivalences` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Factor identifications for the literal three-block regrouping consumer.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockEquivalence`
- `Langlands.AllField.Representation.Induction.SingleBlockSupplement`
- `Langlands.AllField.Representation.Shahidi.Induction`
- `Langlands.AllField.Representation.Tensor.GLRefinement`

## Declarations

- `Langlands.AllField.FiniteTensor.rankCastRepresentationEquiv` (def): The published rank-transport linear map as an actual representation equivalence.
- `Langlands.LocalFieldData.singleBlockTransportedProductEquiv` (def): A one-block product of the canonically transported factor evaluates to that factor.

Public declarations of the original that are not re-declared here: `Langlands.Parabolic.threeBlockSmoothFamily`, `Langlands.Parabolic.threeBlockSmoothFamily_zero`, `Langlands.Parabolic.threeBlockSmoothFamily_one`, `Langlands.Parabolic.threeBlockSmoothFamily_two`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
