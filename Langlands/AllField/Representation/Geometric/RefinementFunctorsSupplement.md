# All-field supplement to `Langlands.AllField.Representation.Geometric.RefinementFunctors`

`Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement` supplements the Library module `Langlands.AllField.Representation.Geometric.RefinementFunctors`, the existing all-field port of `Langlands.Representation.Geometric.RefinementFunctors`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Geometric.RefinementFunctors` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Geometric.RefinementFunctors` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual normalized induction and Jacquet functors inside product Levis.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement`
- `Langlands.AllField.Representation.Geometric.RefinementFunctors`

## Declarations

- `Langlands.LocalFieldData.normalizedRefinedJacquetFunctor` (def): The actual normalized Jacquet functor of a refinement of a product Levi.
- `Langlands.LocalFieldData.normalizedRefinedInduced` (def): The normalized refined induction action uses the positive half of the same modulus.
- `Langlands.LocalFieldData.normalizedRefinedInducedMap` (def): The normalized induced map is postcomposition by the original intertwiner.
- `Langlands.LocalFieldData.normalizedRefinedInductionFunctor` (def): Normalized induction between the actual smooth categories of product Levi subgroups.

Declarations of the original re-declared by `Langlands.AllField.Representation.Geometric.RefinementFunctors` and therefore not here: `Langlands.PadicField.TopologicalData.normalizedRefinedJacquet`, `Langlands.PadicField.TopologicalData.normalizedRefinedJacquet_mk`, `Langlands.PadicField.TopologicalData.normalizedRefinedJacquetMap`.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.refinedLevi_le_normalizer`, `Langlands.Geometric.RefinedJacquetModule`, `Langlands.Geometric.refinedJacquetMk`, `Langlands.Geometric.normalizedRefinedJacquetOf`, `Langlands.Geometric.normalizedRefinedJacquetOf_mk`, `Langlands.Geometric.normalizedRefinedJacquetOfMap`, `Langlands.Geometric.normalizedRefinedJacquetOfMap_mk`, `Langlands.Geometric.isSmooth_normalizedRefinedJacquetOf`, `Langlands.Geometric.normalizedRefinedJacquetFunctorOf`, `Langlands.Geometric.refinedInducingRepresentation`, `Langlands.Geometric.normalizedRefinedInducedOf`, `Langlands.Geometric.normalizedRefinedInducedOf_covariant`, `Langlands.Geometric.normalizedRefinedInducedOf_apply`, `Langlands.Geometric.refinedInducingMap`, `Langlands.Geometric.normalizedRefinedInducedOfMap`, `Langlands.Geometric.normalizedRefinedInducedOfMap_apply`, `Langlands.Geometric.normalizedRefinedInductionFunctorOf`, `Langlands.PadicField.TopologicalData.isSmooth_normalizedRefinedJacquet`, `Langlands.PadicField.TopologicalData.isSmooth_normalizedRefinedInduced`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
