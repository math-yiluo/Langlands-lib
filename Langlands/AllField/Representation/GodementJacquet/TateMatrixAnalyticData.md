# All-field port of `Langlands.Representation.GodementJacquet.TateMatrixAnalyticData`

`Langlands.AllField.Representation.GodementJacquet.TateMatrixAnalyticData` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TateMatrixAnalyticData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TateMatrixAnalyticData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual rank-one matrix analytics from a proved scalar character action.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.MatrixUnitValueProof`
- `Langlands.AllField.Representation.GodementJacquet.TateScalarMellin`
- `Langlands.AllField.Representation.GodementJacquet.TateScalarTransport`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.tateCharacter_mellinAnalyticData` (theorem): The scalar character has actual uniform Mellin analytic data.
- `Langlands.AllField.GodementJacquet.Padic.tateMatrixIntegrand_eq_scalar` (theorem): Scalar and matrix integrands agree after absorbing the coefficient at one
  into the genuine scalar test.
- `Langlands.AllField.GodementJacquet.Padic.tateMatrixIntegral_eq_scalar` (theorem): Equality of the actual integrals uses the exact canonical Haar transport.
- `Langlands.AllField.GodementJacquet.Padic.tateMatrix_characterConverges` (theorem): One convergence half-plane works for all tests and scalar multiples of
  this character, before a coefficient family is specified.
- `Langlands.AllField.GodementJacquet.Padic.tateHasShiftedRationalValue_iff` (theorem): The rank-one shift is zero, and genuine convergence is already proved.
- `Langlands.AllField.GodementJacquet.Padic.exists_tateCharacterCoefficient` (theorem): A genuine coefficient equal to the character, obtained by normalizing a
  nonzero smooth coefficient at the identity.
- `Langlands.AllField.GodementJacquet.Padic.tateMatrixRationalValues_eq_scalar` (theorem): Matrix and scalar rational-value families are equal before taking any span.
- `Langlands.AllField.GodementJacquet.Padic.exists_tateMatrixAnalyticAssertions` (theorem): Uniform matrix convergence, rationality and a normalized generator follow
  from the scalar Mellin theorem and the attained unit value.
- `Langlands.AllField.GodementJacquet.Padic.tateIotaMatrixRationalValues_eq_scalar` (theorem): The transformed value family is exactly the inverse-character Mellin
  family, with the same Haar measure and spectral weight.
- `Langlands.AllField.GodementJacquet.Padic.exists_tateIotaMatrixAnalyticAssertions` (theorem): Transformed convergence, rationality and normalized generation are
  transported from the actual inverse-transpose pullback.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.TateCharacterAction`, `Langlands.GodementJacquet.tateCharacter_translationFinite`, `Langlands.GodementJacquet.tateCoefficient_eq`, `Langlands.GodementJacquet.tateInverseTranspose_eq_inv`, `Langlands.GodementJacquet.tateInverseTranspose_action`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
