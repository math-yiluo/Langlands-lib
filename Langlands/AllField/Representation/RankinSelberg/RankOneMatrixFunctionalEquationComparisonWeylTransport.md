# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual Weyl substitution for matrix integrals and their rational values**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.matrixConverges_weylTranslate_dualFunction_iff` (theorem): Weyl convergence transport for the actual canonical p-adic matrix integral.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.matrixIntegrand_leftTranslate`, `Langlands.GodementJacquet.matrixConverges_leftTranslate_iff`, `Langlands.GodementJacquet.matrixIntegral_leftTranslate`, `Langlands.GodementJacquet.shiftedConvergesOnRight_leftTranslate_iff`, `Langlands.GodementJacquet.hasShiftedRationalValue_leftTranslate_iff`, `Langlands.GodementJacquet.absoluteValue_det_weylLong`, `Langlands.GodementJacquet.matrixWeylTranslate`, `Langlands.GodementJacquet.matrixWeylTranslate_apply`, `Langlands.GodementJacquet.dualFunction_eq_coefficientIota_weyl`, `Langlands.GodementJacquet.matrixConverges_weylTranslate_dualFunction_iff`, `Langlands.GodementJacquet.matrixIntegral_weylTranslate_dualFunction`, `Langlands.GodementJacquet.shiftedConvergesOnRight_weylTranslate_dualFunction_iff`, `Langlands.GodementJacquet.hasShiftedRationalValue_weylTranslate_dualFunction_iff`, `Langlands.GodementJacquet.Padic.matrixIntegral_weylTranslate_dualFunction`, `Langlands.GodementJacquet.Padic.shiftedConvergesOnRight_weylTranslate_dualFunction_iff`, `Langlands.GodementJacquet.Padic.hasShiftedRationalValue_weylTranslate_dualFunction_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
