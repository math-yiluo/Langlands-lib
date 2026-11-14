# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourier`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourier` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourier`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourier` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Fourier covariance of actual supercuspidal cutoff coefficients**

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffTests`

## Declarations

- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_right` (theorem).
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_fourier_right` (theorem): The Fourier integral of the actual cutoff is covariant under every
  determinant-unit right translate of the representation vector.
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffFourierEvaluation` (def): Actual Fourier evaluation of the cutoff as a linear functional in its vector.
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer` (theorem): A Fourier evaluation fixed by a subgroup with zero Jacquet quotient is zero.
  No averaging or quotient measure is used.
- `Langlands.AllField.GodementJacquet.determinantNorm_eq_one_of_mem_conjugateUnipotent` (theorem): Every conjugate block radical has determinant norm one.
