# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalOperatorComparison`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalOperatorComparison` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalOperatorComparison`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalOperatorComparison` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Descending the Fourier-regular operator comparison**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalMonomialOutputs`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.fourierRegularMatrixZetaOperator` (def): Restrict the actual compact zeta operator to Fourier-regular tests.
- `Langlands.AllField.GodementJacquet.Padic.fourierRegularMatrixZetaOperator_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.fourierRegularMatrixZetaOperator_separates` (theorem): The Fourier-regular operator family has zero common kernel at every
  exponent, by the nonzero constant-output witness on a chosen nonzero input.
- `Langlands.AllField.GodementJacquet.Padic.fourierRegularMatrixZetaOperator_output_surjective` (theorem): At every exponent the finite-output presentation is surjective, because
  the monomial outputs on one nonzero input span and spectral powers are nonzero.
- `Langlands.AllField.GodementJacquet.Padic.intertwining_of_commutes_fourierRegularMatrixZetaOperator` (theorem): A comparison that commutes with all Fourier-regular test operators
  commutes with the representation, by left translation and output spanning.
- `Langlands.AllField.GodementJacquet.Padic.exists_scalar_of_fourierRegularMatrixZetaOperator_cross` (theorem): For the actual Fourier-regular operator family, the cross identity
  forces any comparison family to be a single scalar multiple at each exponent.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.operatorFamilyLinearCombination`, `Langlands.GodementJacquet.operatorFamilyLinearCombination_single`, `Langlands.GodementJacquet.operatorFamilyLinearCombination_ker_le`, `Langlands.GodementJacquet.operatorFamilyComparison`, `Langlands.GodementJacquet.operatorFamilyComparison_apply_output`, `Langlands.GodementJacquet.operatorFamilyComparison_commutes`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
