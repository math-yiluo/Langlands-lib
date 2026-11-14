# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationalExtension`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixRationalExtension` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationalExtension`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationalExtension` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The rational supercuspidal equation for arbitrary matrix tests**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.FourierRegularRationalEquation`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixPairingExtension`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.reflectedIotaFourierMatrixCoefficientRationalPairing` (def): The actual chosen Fourier and inverse-transpose rational pairing after
  the normalized spectral reflection `X ↦ q⁻¹/X`.
- `Langlands.AllField.GodementJacquet.Padic.reflectedIotaFourierMatrixCoefficientRationalPairing_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.reflectedIotaFourierMatrixCoefficientRationalPairing_translate` (theorem): Rational spectral reflection preserves the norm-one translation rule.
- `Langlands.AllField.GodementJacquet.Padic.matrixRationalPairing_identity_of_supercuspidal_fourierRegular_operator` (theorem): The global Fourier-regular operator equation extends to the actual
  reflected rational pairings for every full-matrix test.
- `Langlands.AllField.GodementJacquet.Padic.normalizedFunctionalEquation_of_supercuspidal_fourierRegular_operator` (theorem): For arbitrary full-matrix tests and a fixed coefficient functional, the
  same shifted monomial gives the normalized equation for all supplied actual
  original and Fourier-dual rational values.
