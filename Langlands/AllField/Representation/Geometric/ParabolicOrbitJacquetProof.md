# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitJacquetProof`

`Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquetProof` is the all-field port of the Library module `Langlands.Representation.Geometric.ParabolicOrbitJacquetProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Geometric.ParabolicOrbitJacquetProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The natural normalized comparison for the actual parabolic orbit.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.ParabolicOrbitCompactComparison`
- `Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquetStatement`

## Declarations

- `Langlands.LocalFieldData.parabolicOrbitJacquetComparison` (theorem): The actual orbit integral, target normalization and refined induction form
  one natural isomorphism on the full smooth source category.
- `Langlands.AllField.Geometric.padicParabolicOrbitJacquetComparison` (theorem): BZ77's local comparison, with all normalizing characters cancelled, for
  all supplied actual p-adic data and all smooth complex source representations.
