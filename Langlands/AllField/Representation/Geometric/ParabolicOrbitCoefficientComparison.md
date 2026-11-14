# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison`

`Langlands.AllField.Representation.Geometric.ParabolicOrbitCoefficientComparison` is the all-field port of the Library module `Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual coefficient quotients for a parabolic orbit.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.AllField.Representation.Geometric.StandardIntersectionsProof`
- `Langlands.AllField.Representation.Parabolic.RefinementCharacter`

## Declarations

- `Langlands.LocalFieldData.sourceUnipotent_le_ker_leviHalfModulus` (theorem): The genuine source induction character is trivial on the actual source
  radical intersection, using the supplied unipotent refinement equality.
- `Langlands.LocalFieldData.parabolicOrbitRefinedCoefficientEquiv` (def): The actual positive-half inducing coefficient has exactly the refined
  source Jacquet carrier as its radical quotient.
- `Langlands.LocalFieldData.parabolicOrbitRefinedCoefficientEquiv_mk` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.Geometric.parabolicOrbitCoefficientRadical`, `Langlands.Geometric.parabolicOrbitCoefficientRadicalEquiv`, `Langlands.Geometric.parabolicOrbitCoefficientRadical_map`, `Langlands.Geometric.parabolicOrbitCoefficient`, `Langlands.Geometric.parabolicOrbitCoefficientEquiv`, `Langlands.Geometric.parabolicOrbitCoefficientEquiv_mk`, `Langlands.Geometric.parabolicOrbitCoefficientEquiv_symm_mk`, `Langlands.Geometric.parabolicOrbitCoefficientMap`, `Langlands.Geometric.parabolicOrbitCoefficientEquiv_natural`, `Langlands.Geometric.sourceLevi_le_normalizer_sourceUnipotent`, `Langlands.Geometric.parabolicOrbitIntersectionSection`, `Langlands.Geometric.parabolicOrbitToSourceLevi_intersectionSection`, `Langlands.Geometric.parabolicOrbitCoefficientAction`, `Langlands.Geometric.parabolicOrbitCoefficientActionEquiv`, `Langlands.Geometric.parabolicOrbitCoefficientActionEquiv_mk`, `Langlands.PadicField.TopologicalData.parabolicOrbitRefinedCoefficientEquiv_symm_mk`, `Langlands.PadicField.TopologicalData.parabolicOrbitRefinedCoefficientEquiv_natural`, `Langlands.PadicField.TopologicalData.parabolicOrbitRefinedCoefficientEquiv_section_mk`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
