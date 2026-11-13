# All-field port of `Langlands.Representation.Geometric.RefinementFunctors`

`Langlands.AllField.Representation.Geometric.RefinementFunctors` is the all-field port of the Library module `Langlands.Representation.Geometric.RefinementFunctors`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Geometric.RefinementFunctors` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual normalized induction and Jacquet functors inside product Levis.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.RefinementDefinitions`

## Declarations

- `Langlands.LocalFieldData.normalizedRefinedJacquet` (def): The actual local-field refined Jacquet action, with the explicit full product modulus.
- `Langlands.LocalFieldData.normalizedRefinedJacquet_mk` (theorem): Its action on quotient classes uses the canonical inverse half.
- `Langlands.LocalFieldData.normalizedRefinedJacquetMap` (def): Refined Jacquet maps preserve the actual quotient representatives.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.refinedLevi_le_normalizer`, `Langlands.Geometric.RefinedJacquetModule`, `Langlands.Geometric.refinedJacquetMk`, `Langlands.Geometric.normalizedRefinedJacquetOf`, `Langlands.Geometric.normalizedRefinedJacquetOf_mk`, `Langlands.Geometric.normalizedRefinedJacquetOfMap`, `Langlands.Geometric.normalizedRefinedJacquetOfMap_mk`, `Langlands.Geometric.isSmooth_normalizedRefinedJacquetOf`, `Langlands.Geometric.normalizedRefinedJacquetFunctorOf`, `Langlands.Geometric.refinedInducingRepresentation`, `Langlands.Geometric.normalizedRefinedInducedOf`, `Langlands.Geometric.normalizedRefinedInducedOf_covariant`, `Langlands.Geometric.normalizedRefinedInducedOf_apply`, `Langlands.Geometric.refinedInducingMap`, `Langlands.Geometric.normalizedRefinedInducedOfMap`, `Langlands.Geometric.normalizedRefinedInducedOfMap_apply`, `Langlands.Geometric.normalizedRefinedInductionFunctorOf`, `Langlands.PadicField.TopologicalData.isSmooth_normalizedRefinedJacquet`, `Langlands.PadicField.TopologicalData.normalizedRefinedJacquetFunctor`, `Langlands.PadicField.TopologicalData.normalizedRefinedInduced`, `Langlands.PadicField.TopologicalData.isSmooth_normalizedRefinedInduced`, `Langlands.PadicField.TopologicalData.normalizedRefinedInducedMap`, `Langlands.PadicField.TopologicalData.normalizedRefinedInductionFunctor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
