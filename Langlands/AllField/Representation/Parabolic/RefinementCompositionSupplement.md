# All-field supplement to `Langlands.AllField.Representation.Parabolic.RefinementComposition`

`Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement` supplements the Library module `Langlands.AllField.Representation.Parabolic.RefinementComposition`, the existing all-field port of `Langlands.Representation.Parabolic.RefinementComposition`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.Parabolic.RefinementComposition` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinementComposition` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The actual composite parabolic for a refinement of an ordered block shape.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement`
- `Langlands.AllField.Representation.Parabolic.RefinementComposition`

## Declarations

- `Langlands.LocalFieldData.refinedOuterModulus_projection` (theorem): The outer modulus factors through the actual inner Levi projection.
- `Langlands.LocalFieldData.refinedOuterHalfModulus_projection` (theorem).
- `Langlands.LocalFieldData.composedParabolicHalfModulus` (def): The positive induction character on the actual composite parabolic.

Declarations of the original re-declared by `Langlands.AllField.Representation.Parabolic.RefinementComposition` and therefore not here: `Langlands.PadicField.TopologicalData.composedLeviModulus`, `Langlands.PadicField.TopologicalData.composedLeviHalfModulus`, `Langlands.PadicField.TopologicalData.composedLeviHalfModulus_eq`.

Public declarations of the original that are not re-declared here: `Langlands.Parabolic.composedParabolic`, `Langlands.Parabolic.composedUnipotent`, `Langlands.Parabolic.composedLeviProjection`, `Langlands.Parabolic.composedLeviSection`, `Langlands.Parabolic.composedLeviSection_val`, `Langlands.Parabolic.composedLeviProjection_section`, `Langlands.Parabolic.composedLeviProjection_surjective`, `Langlands.Parabolic.composedLeviProjection_ker_map`, `Langlands.Parabolic.composedLeviProjection_ker`, `Langlands.Parabolic.composedUnipotent_le_parabolic`, `Langlands.Parabolic.composedParabolic_le_normalizer`, `Langlands.Parabolic.composedLeviNormalizer`, `Langlands.Parabolic.composedLeviNormalizer_val`, `Langlands.Parabolic.composedUnipotentPart`, `Langlands.Parabolic.composedDecomposition`, `Langlands.Parabolic.composedLeviProjectionContinuous`, `Langlands.Parabolic.composedLeviSectionContinuous`, `Langlands.Parabolic.composedLeviNormalizerContinuous`, `Langlands.PadicField.TopologicalData.inverseHalf_composedLeviModulus`, `Langlands.PadicField.TopologicalData.isOpen_ker_composedLeviModulus`, `Langlands.PadicField.TopologicalData.isOpen_ker_composedLeviHalfModulus`, `Langlands.PadicField.TopologicalData.isOpen_ker_composedParabolicHalfModulus`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
