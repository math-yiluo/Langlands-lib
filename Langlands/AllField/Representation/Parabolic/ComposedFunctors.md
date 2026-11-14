# All-field port of `Langlands.Representation.Parabolic.ComposedFunctors`

`Langlands.AllField.Representation.Parabolic.ComposedFunctors` is the all-field port of the Library module `Langlands.Representation.Parabolic.ComposedFunctors`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.ComposedFunctors` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Direct normalized functors for the actual composed matrix parabolic.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement`

## Declarations

- `Langlands.LocalFieldData.composedInducingRepresentation` (abbrev): Inflation through the actual composite projection, with the positive half.
- `Langlands.LocalFieldData.normalizedComposedInduced` (def): Direct smooth induction from the smaller actual matrix parabolic.
- `Langlands.LocalFieldData.composedInducingMap` (def): Inflate and twist an intertwiner using the composite projection.
- `Langlands.LocalFieldData.normalizedComposedInducedMap` (def): The direct induced intertwiner acts by pointwise postcomposition.
- `Langlands.LocalFieldData.isSmooth_normalizedComposedInduced` (theorem).
- `Langlands.LocalFieldData.normalizedComposedInductionFunctor` (def): Direct normalized induction between the actual smooth categories.

Public declarations of the original that are not re-declared here: `Langlands.Parabolic.ComposedJacquetModule`, `Langlands.Parabolic.composedJacquetMk`, `Langlands.Parabolic.composedJacquetAction`, `Langlands.Parabolic.composedJacquetAction_mk`, `Langlands.Parabolic.composedJacquetMap`, `Langlands.Parabolic.composedJacquetMap_mk`, `Langlands.Parabolic.isSmooth_composedJacquetAction`, `Langlands.PadicField.TopologicalData.normalizedComposedJacquet`, `Langlands.PadicField.TopologicalData.normalizedComposedJacquet_mk`, `Langlands.PadicField.TopologicalData.normalizedComposedJacquetMap`, `Langlands.PadicField.TopologicalData.normalizedComposedJacquetMap_mk`, `Langlands.PadicField.TopologicalData.isSmooth_normalizedComposedJacquet`, `Langlands.PadicField.TopologicalData.normalizedComposedJacquetFunctor`, `Langlands.PadicField.TopologicalData.normalizedComposedInduced_covariant`, `Langlands.PadicField.TopologicalData.normalizedComposedInduced_apply`, `Langlands.PadicField.TopologicalData.normalizedComposedInducedMap_apply`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
