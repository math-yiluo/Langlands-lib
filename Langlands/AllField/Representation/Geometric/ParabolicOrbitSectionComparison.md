# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitSectionComparison`

`Langlands.AllField.Representation.Geometric.ParabolicOrbitSectionComparison` is the all-field port of the Library module `Langlands.Representation.Geometric.ParabolicOrbitSectionComparison`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Geometric.ParabolicOrbitSectionComparison` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The full intermediate section factors through the target refined Levi.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.ParabolicOrbitStagesCoefficient`

## Declarations

- `Langlands.LocalFieldData.parabolicOrbitSectionCharacter` (def): The two source positive halves retained before the Haar and target corrections.
- `Langlands.LocalFieldData.parabolicOrbitFullRefinedCoefficientActionEquiv` (def): The full actual coefficient action identifies with normalized refined Jacquet
  action and the two explicit source positive halves.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.parabolicOrbitStagesRefinedEquiv`, `Langlands.Geometric.parabolicOrbitStagesRefinedEquiv_val`, `Langlands.Geometric.parabolicOrbitStagesRefinedEquiv_symm_val`, `Langlands.Geometric.parabolicOrbitRefinedSection`, `Langlands.Geometric.parabolicOrbitRefinedSourceCoordinate`, `Langlands.Geometric.parabolicOrbitRefinedSourceCoordinate_unipotent`, `Langlands.Geometric.parabolicOrbitRefinedSection_levi`, `Langlands.Geometric.parabolicOrbitRefinedSourceCoordinate_levi`, `Langlands.Geometric.parabolicOrbitRefinedSourceCoordinate_factor`, `Langlands.Geometric.parabolicOrbitTargetLeviProjection`, `Langlands.Geometric.parabolicOrbitSourceLeviCoordinate`, `Langlands.Geometric.parabolicOrbitToSourceLevi_stagesSection`, `Langlands.Geometric.parabolicOrbitFullCoefficientAction`, `Langlands.Geometric.parabolicOrbitFullCoefficientActionEquiv`, `Langlands.Geometric.parabolicOrbitFullCoefficientActionEquiv_mk`, `Langlands.Geometric.parabolicOrbitFullCoefficientActionEquiv_natural`, `Langlands.Geometric.parabolicOrbitNestedCoefficientEquiv_projected_section_mk`, `Langlands.Geometric.parabolicOrbitSourceRefinedCoordinate`, `Langlands.Geometric.parabolicOrbitSourceRefinedCoordinate_val`, `Langlands.Geometric.parabolicOrbitStagesRefinedEquivContinuous`, `Langlands.Geometric.continuous_parabolicOrbitTargetLeviProjection`, `Langlands.Geometric.continuous_parabolicOrbitSourceLeviCoordinate`, `Langlands.Geometric.continuous_parabolicOrbitSourceRefinedCoordinate`, `Langlands.PadicField.TopologicalData.parabolicOrbitNestedRefinedCoefficientEquiv_projected_section_mk`, `Langlands.PadicField.TopologicalData.parabolicOrbitFullRefinedCoefficientActionEquiv_mk`, `Langlands.PadicField.TopologicalData.parabolicOrbitFullRefinedCoefficientActionEquiv_natural`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
