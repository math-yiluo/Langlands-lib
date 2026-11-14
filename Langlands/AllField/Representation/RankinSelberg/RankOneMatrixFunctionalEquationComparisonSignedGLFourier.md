# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The actual signed Fourier exchange on unipotent times general linear groups**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLFourierBridge`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitFourier`

## Declarations

- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.signedUnipotentGeneralLinearFourierDualKernel` (def): The actual dual Fourier orbit kernel with the natural GL determinant weight.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.signedUnipotentGeneralLinearFourierOriginalKernel` (def): The original orbit kernel with the identical natural GL determinant weight.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_generalLinear_signedUnipotentMatrixFourierDualKernel` (theorem): Actual inverse-transpose/Weyl dual kernel convergence on N × GL, without
  any invertible-support premise on the Fourier transform of Φ.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel` (theorem): Actual original kernel convergence on N × GL, from invertible support of
  Φ and no additional support premise on Ψ.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integral_generalLinear_signedUnipotentMatrixFourierDualKernel` (theorem): Each actual dual product integral has the same inverse scalar as every
  other weighted GL integral, with no test-dependent normalization.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel` (theorem): The original product integral uses exactly the same normalization.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.generalLinear_signedUnipotentMatrixFourier_exchange` (theorem): Actual weighted Fourier exchange on N × GL; both product integrabilities
  are proved and the identical normalization scalars cancel.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.GLDeterminantDensity.generalLinear_signedUnipotentMatrixFourier_exchange_averaged`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
