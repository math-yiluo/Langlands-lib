# All-field port of `Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation`

`Langlands.AllField.Representation.GodementJacquet.TateScalarFunctionalEquation` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Scalar Tate functional equation from the independent equal-rank theorem.

## Imports from the port

- `Langlands.AllField.LocalFactor.ResidueReflection`
- `Langlands.AllField.Representation.GodementJacquet.TateScalarMellin`
- `Langlands.AllField.Representation.GodementJacquet.TateScalarTransport`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFunctionalEquationProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero`
- `Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.tateEqualRankIntegral_eq_scalar` (theorem): Original model integrals are scalar Mellin integrals, with the two vector
  coordinates absorbed into the test.
- `Langlands.AllField.GodementJacquet.Padic.tateDualEqualRankIntegral_eq_scalar` (theorem): The transformed model integrals use the inverse multiplicative character.
- `Langlands.AllField.GodementJacquet.Padic.tateCharacterModelOne_at_one` (theorem): The coefficient of the unit vector is normalized at the identity.
- `Langlands.AllField.GodementJacquet.Padic.tateTrivialModelOne_at_one` (theorem): The trivial coefficient of the unit vector is normalized at the identity.
- `Langlands.AllField.GodementJacquet.Padic.tateEqualRankIntegral_unit_eq_scalar` (theorem): At unit model vectors, only the row-to-scalar test transport remains.
- `Langlands.AllField.GodementJacquet.Padic.tateDualEqualRankIntegral_unit_eq_scalar` (theorem): The unit dual model vectors give exactly the inverse-character Mellin test.
- `Langlands.AllField.GodementJacquet.Padic.tateEqualRankRationalValues_eq_scalar` (theorem): Equality of the complete original rational-value families.
- `Langlands.AllField.GodementJacquet.Padic.tateDualEqualRankRationalValues_eq_scalar` (theorem): Equality of the complete dual rational-value families.
- `Langlands.AllField.GodementJacquet.Padic.tateScalarFunctionalEquation` (theorem): The scalar Tate functional equation for the exact supplied self-dual Haar
  measure. The epsilon constant and exponent are chosen before every scalar test;
  the equation holds for every pair of its actual rational continuations.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.tateRowScalarHomeomorph`, `Langlands.GodementJacquet.tateRowTest`, `Langlands.GodementJacquet.tateScalarRowTest`, `Langlands.GodementJacquet.tateRowTest_apply`, `Langlands.GodementJacquet.tateScalarRowTest_apply`, `Langlands.GodementJacquet.tateScalarRowTest_tateRowTest`, `Langlands.GodementJacquet.tateCharacterFunctional`, `Langlands.GodementJacquet.tateCharacterFunctional_ne_zero`, `Langlands.GodementJacquet.tateCharacterModel_apply`, `Langlands.GodementJacquet.rowFourierIntegral_tateRowTest`, `Langlands.GodementJacquet.tateScalarFourierPair_of_row`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
