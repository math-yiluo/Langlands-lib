# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalMonomialOutputs`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalMonomialOutputs` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalMonomialOutputs`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalMonomialOutputs` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Cyclic monomial outputs of Fourier-regular matrix tests**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.FourierRegularMatrixTranslates`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.weightedRegularMatrixTest_leftTranslate` (theorem): The exact determinant factor for the weighted left translate.
- `Langlands.AllField.GodementJacquet.Padic.regularMatrixZetaOperator_leftTranslate` (theorem): Left translation acts on the actual operator output by the representation
  and its determinant weight.
- `Langlands.AllField.GodementJacquet.Padic.regularMatrixZetaOperator_eq_of_detNorm_support` (theorem): A regular test supported on determinant norm one gives an operator
  independent of the complex exponent.
- `Langlands.AllField.GodementJacquet.Padic.exists_fourierRegular_constant_output_of_pairing` (theorem): For any nonzero smooth pairing, one Fourier-regular test has the same
  nonzero output on the chosen vector at every exponent.
- `Langlands.AllField.GodementJacquet.Padic.exists_fourierRegular_constant_output` (theorem): Smooth dual separation supplies the nonzero pairing for every nonzero input
  vector, retaining that same input in all the resulting operator evaluations.
- `Langlands.AllField.GodementJacquet.Padic.fourierRegularMonomialOutputs` (def): Outputs on one fixed input that are realized by an actual Fourier-regular
  test at every exponent, up to one integer spectral power.
- `Langlands.AllField.GodementJacquet.Padic.representation_mem_fourierRegularMonomialOutputs` (theorem): Translating a realizing test realizes the translated output with the sum
  of its old exponent and the determinant order of the translating element.
- `Langlands.AllField.GodementJacquet.Padic.span_fourierRegularMonomialOutputs_eq_top` (theorem): For a nonzero fixed input in an irreducible supercuspidal representation
  of rank at least two, the monomial outputs span the whole carrier.
