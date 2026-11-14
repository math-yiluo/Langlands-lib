# All-field port of `Langlands.Representation.GodementJacquet.ContinuedMatrixCovariance`

`Langlands.AllField.Representation.GodementJacquet.ContinuedMatrixCovariance` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.ContinuedMatrixCovariance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.ContinuedMatrixCovariance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Norm-one covariance of continued matrix pairings**

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate`
- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.matrixCoefficientRationalPairing` (def): The original actual shifted rational matrix integral, bilinear in the
  full-matrix test and the representation vector, for a fixed functional.
- `Langlands.AllField.GodementJacquet.Padic.matrixCoefficientRationalPairing_spec` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.matrixCoefficientRationalPairing_translate` (theorem): The original rational pairing has the covariance used in compact smoothing
  transfer, with the inverse action on the vector.
- `Langlands.AllField.GodementJacquet.Padic.matrixFourierEquiv_translate_of_norm_one` (theorem): The actual full Fourier equivalence commutes with norm-one right
  translation after replacing the translating matrix by its inverse transpose.
- `Langlands.AllField.GodementJacquet.Padic.iotaFourierMatrixCoefficientRationalPairing` (def): The actual inverse-transpose coefficient pairing after the full plus
  Fourier transform, before reflection in the rational spectral variable.
- `Langlands.AllField.GodementJacquet.Padic.iotaFourierMatrixCoefficientRationalPairing_spec` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.iotaFourierMatrixCoefficientRationalPairing_translate` (theorem): The Fourier and inverse-transpose operations cancel their changes to the
  right action, giving the same covariance as the original rational pairing.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.matrixIntegral_translate_of_norm_one`, `Langlands.GodementJacquet.matrixRationalPairing_translate_of_norm_one`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
