# All-field port of `Langlands.Representation.GodementJacquet.CentralMatrixRationality`

`Langlands.AllField.Representation.GodementJacquet.CentralMatrixRationality` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.CentralMatrixRationality`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.CentralMatrixRationality` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rational continuation from compact scalar covers**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.CompactMatrixLaurent`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.matrixGeometricDenominator` (def): The common central geometric denominator, in the exact shifted spectral variable.
- `Langlands.AllField.GodementJacquet.Padic.laurentEval_matrixGeometricDenominator` (theorem): Spectral evaluation gives precisely the analytic recurrence denominator.
- `Langlands.AllField.GodementJacquet.Padic.exists_laurent_matrixIntegral_quotient` (theorem): The compact central difference has an everywhere convergent Laurent value;
  the original integral is its geometric quotient wherever the ratio contracts.
- `Langlands.AllField.GodementJacquet.Padic.matrixGeometricDenominator_ne_zero` (theorem): The common geometric denominator is nonzero for every determinant contraction.
- `Langlands.AllField.GodementJacquet.Padic.exists_shiftedRationalValue_of_scalarSaturation` (theorem): Actual shifted rational continuation, with one common Laurent denominator
  and an explicit numerator clearing identity.
