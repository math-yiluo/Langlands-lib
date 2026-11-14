# All-field port of `Langlands.Representation.RankinSelberg.EqualRankCompactTest`

`Langlands.AllField.Representation.RankinSelberg.EqualRankCompactTest` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankCompactTest`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankCompactTest` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Existence of compact equal-rank coefficient tests**

The compact-test existence predicate uses the actual coefficient images.
Its construction is conditional on canonical Kirillov lifting in the two
independent representation universes.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.AllField.Representation.Whittaker.CoefficientRightStabilizer`
- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof`
- `Langlands.AllField.Representation.Whittaker.ModelKirillovProof`

## Declarations

- `Langlands.AllField.RankinSelberg.hasEqualRankCompactTest_of_kirillov` (theorem): The published mirabolic tests, topology-transfer theorem, common right
  stabilizer and row indicator construct actual compact coefficient tests.
  Canonical Kirillov remains an explicit premise in each carrier universe.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.HasEqualRankCompactTest`, `Langlands.RankinSelberg.HasEqualRankCompactTest.one_mem_equalRankRationalValues`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
