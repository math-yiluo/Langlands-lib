# All-field port of `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement`

`Langlands.AllField.Representation.Parabolic.RefinementCoordinatesNormalizationStatement` is the all-field port of the Library module `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Normalization and actual induced functions under ordered refinement coordinates.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.WeylStatementSupplement`
- `Langlands.AllField.Representation.Induction.Parabolic`
- `Langlands.AllField.Representation.Parabolic.ComposedFunctors`

## Declarations

- `Langlands.AllField.Parabolic.RefinementCoordinatesNormalization.ModulusClause` (def): The full positive modulus agrees after the concrete Levi coordinate map.
- `Langlands.AllField.Parabolic.RefinementCoordinatesNormalization.HalfModulusClause` (def): Both the Levi positive half and its parabolic inflation agree under the
  published coordinate maps. These are equalities of the canonical halves.
- `Langlands.AllField.Parabolic.RefinementCoordinatesNormalization.InductionClause` (def): An actual equivariant linear equivalence of the two smooth induced spaces,
  retaining the underlying ambient function in both directions.
- `Langlands.AllField.Parabolic.RefinementCoordinatesNormalizationTheorem` (def): Full modulus, canonical positive halves and actual induced-function comparison
  for every ordered refinement satisfying the exact coordinate identity.
