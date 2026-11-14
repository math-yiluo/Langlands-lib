# All-field port of `Langlands.Representation.GodementJacquet.AnalyticData`

`Langlands.AllField.Representation.GodementJacquet.AnalyticData` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.AnalyticData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.AnalyticData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual matrix analytic assertions and transpose Fourier data**

These predicates record common shifted convergence, actual rational
continuations, normalized generators and the transpose Fourier functional
equation. They assert no existence theorem, including for reducible carriers.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.Zeta`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.iotaMatrixRationalValues` (def): Transformed values with the canonical p-adic normalizations of `Zeta`.
- `Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight` (def): Common shifted convergence with canonical topology and normalized group Haar measure.
- `Langlands.AllField.GodementJacquet.Padic.IotaMatrixConvergesOnRight` (def): Common transformed shifted convergence with the same canonical group measure.
- `Langlands.AllField.GodementJacquet.Padic.IsMatrixNormalizedGenerator` (def): A proposed normalized generator for the canonical published matrix values.
- `Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions` (def): Actual matrix analytic assertions with all canonical p-adic normalizations.
- `Langlands.AllField.GodementJacquet.Padic.IotaMatrixAnalyticAssertions` (def): Transformed analytic assertions with the same canonical p-adic normalizations.
- `Langlands.AllField.GodementJacquet.Padic.MatrixFourierPair` (def): The actual plus transpose Fourier relation with canonical Borel structures.
  The scalar additive measure is supplied, with no normalization change.
- `Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData` (def): Canonical p-adic functional-equation data retaining the supplied scalar
  Fourier measure. Self-duality is a premise for later existence theorems.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.coefficientIota`, `Langlands.GodementJacquet.iotaMatrixRationalValues`, `Langlands.GodementJacquet.MatrixConvergesOnRight`, `Langlands.GodementJacquet.IotaMatrixConvergesOnRight`, `Langlands.GodementJacquet.IsMatrixNormalizedGenerator`, `Langlands.GodementJacquet.IsIotaMatrixNormalizedGenerator`, `Langlands.GodementJacquet.MatrixAnalyticAssertions`, `Langlands.GodementJacquet.IotaMatrixAnalyticAssertions`, `Langlands.GodementJacquet.MatrixFourierPair`, `Langlands.GodementJacquet.NormalizedMatrixFunctionalEquationData`, `Langlands.GodementJacquet.Padic.IsIotaMatrixNormalizedGenerator`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
