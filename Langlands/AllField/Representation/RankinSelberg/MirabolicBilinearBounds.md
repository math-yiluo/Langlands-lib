# All-field port of `Langlands.Representation.RankinSelberg.MirabolicBilinearBounds`

`Langlands.AllField.Representation.RankinSelberg.MirabolicBilinearBounds` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.MirabolicBilinearBounds`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.MirabolicBilinearBounds` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual mirabolic specialization and translation of finite spectral exceptions.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`
- `Langlands.AllField.Representation.Whittaker.MirabolicFunctionalTransfer`

## Declarations

- `Langlands.AllField.RankinSelberg.mirabolic_exists_exception_length_le_one` (theorem): Finite mirabolic length and irreducible pair control give the full bilinear
  bound for actual restrictions of representations with one-dimensional functionals.
- `Langlands.AllField.RankinSelberg.mirabolic_shift_length_bound` (theorem): The minus-parameter mirabolic bound supplies the exact Frobenius weight `1-s`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.shiftedSpectralExceptions`, `Langlands.RankinSelberg.not_mem_of_not_mem_shiftedSpectralExceptions`, `Langlands.RankinSelberg.exists_finite_exception_shift`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
