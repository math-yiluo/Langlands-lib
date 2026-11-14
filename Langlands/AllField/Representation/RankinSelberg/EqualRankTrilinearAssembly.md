# All-field port of `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly`

`Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Conditional assembly for actual row Schwartz functions and coefficient models.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TrilinearReduction.source_uniqueness_of_mirabolic_bound` (theorem): The actual row-action reduction, with its two finite exceptional sets and
  its weight-shifted Frobenius equivalence left as explicit mathematical inputs.
- `Langlands.AllField.RankinSelberg.TrilinearReduction.equalRankTrilinearUniqueness_of_source` (theorem): The parent target follows from a uniform source-carrier uniqueness bound.
  The bound is an outstanding representation-theoretic input, not a proved fact.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TrilinearReduction.invariantForms`, `Langlands.RankinSelberg.TrilinearReduction.restrictInvariant`, `Langlands.RankinSelberg.TrilinearReduction.PointwiseInvariant`, `Langlands.RankinSelberg.TrilinearReduction.invariant_iff_pointwise`, `Langlands.RankinSelberg.TrilinearReduction.coefficientModel_uniqueness_of_source`, `Langlands.RankinSelberg.TrilinearReduction.restriction_uniqueness_of_bilinear_equiv`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
