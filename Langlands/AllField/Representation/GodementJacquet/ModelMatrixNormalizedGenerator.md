# All-field port of `Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator`

`Langlands.AllField.Representation.GodementJacquet.ModelMatrixNormalizedGenerator` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized matrix generators on actual Whittaker coefficient models**

Transport the published rank-one pair L-polynomial through `I₁ = I₃ = I₂`.
The carrier is the actual coefficient image, with no irreducibility premise.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.WhittakerModelComparisonProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof`
- `Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.isMatrixNormalizedGenerator_model_of_character` (theorem): A character L-generator is the ordinary matrix generator on every
  nonzero coefficient model, by the two published ideal comparisons.
- `Langlands.AllField.GodementJacquet.Padic.isMatrixNormalizedGenerator_model_of_pair` (theorem): One full symmetric pair certificate supplies the ordinary normalized
  matrix generator on every nonzero actual coefficient model.
- `Langlands.AllField.GodementJacquet.Padic.exists_modelMatrixNormalizedGenerator` (theorem): Existence retains the complete symmetric L-certificate and gives a
  single polynomial for all nonzero functionals on the original carrier.
- `Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial` (def): The ordinary matrix polynomial chosen from the full pair L-existence
  theorem. Its generator property concerns the actual coefficient models.
- `Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial_pair` (theorem): The chosen polynomial retains the full supplied-measure pair certificate.
- `Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial_normalized` (theorem): The chosen polynomial generates the ordinary matrix values on each
  actual nonzero coefficient model of the original representation.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.IsPairLPolynomial.isCharacterLPolynomial`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
