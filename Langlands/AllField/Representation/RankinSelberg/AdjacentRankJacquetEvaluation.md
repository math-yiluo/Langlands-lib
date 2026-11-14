# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJacquetEvaluation`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetEvaluation` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetEvaluation`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetEvaluation` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankDoubleIntegral`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankNormalizedSection`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentJacquet.determinantWeight_eq` (theorem): The smooth determinant character agrees with the exact scalar integral weight.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.sectionCoefficient` (def): Scalar evaluation of an actual normalized section through the original module.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrand` (def): The literal scalar Jacquet kernel, with the inverse last-coordinate phase.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.sectionCoefficient_normalizedSection` (theorem): Pure normalized sections retain their original-carrier algebraic average
  after scalar evaluation.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrand_normalizedSection` (theorem): The actual pure-section Jacquet kernel is the translated literal inner
  integral, with precisely the ambient normalized determinant weight.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrable_normalizedSection_realTwist` (theorem): Actual scalar Jacquet integrability of every pure normalized compact section
  uses the same representation-uniform threshold as the double integral.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integral_normalizedSection_eq_doubleIntegral` (theorem): Scalar integration of a pure normalized section retains the literal
  iterated double integral, including its exact outer determinant weight.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integral_normalizedSection_eq_modelIntegral` (theorem): The actual Jacquet integral on each pure original-carrier normalized section
  is precisely the published pure-tensor model integral, as a function of every g.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.AdjacentJacquet.upperColumn`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_castSucc_castSucc`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_castSucc_last`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_last_castSucc`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_last_last`, `Langlands.RankinSelberg.AdjacentJacquet.determinant_upperColumn`, `Langlands.RankinSelberg.AdjacentJacquet.rectangularJoin_mul_upperColumn`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
