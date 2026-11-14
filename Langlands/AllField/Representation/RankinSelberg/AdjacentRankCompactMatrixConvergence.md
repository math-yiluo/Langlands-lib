# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixIntegrability`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.realTwistedCharacter` (def): The exact real spectral twist used in the adjacent-rank image statement.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.norm_realSpectralCharacter` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.exists_character_norm_exponent` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.characterNormExponent` (def): The unique real norm exponent of the arbitrary continuous base character.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.characterNormExponent_spec` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.norm_realTwistedCharacter` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.norm_realDeterminantWeight` (theorem): The norm of a real determinant weight is its real power.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.determinantWeight_add_exponents` (theorem): Multiplication of determinant weights at the strictly positive determinant norm.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.integrable_of_compact_det_growth` (theorem): Compact square-matrix tests become GL Haar integrable as soon as the
  character and determinant powers dominate the coefficient pole and Haar density.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.realTwistThreshold` (def): A single sufficient real-twist threshold chosen before coefficient vectors
  and square-matrix tests. No optimality is asserted.
- `Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.integrable_realTwist_of_threshold` (theorem): The exact real spectral twists give genuine GL Haar integrability for
  every coefficient vector and every square-matrix Schwartz--Bruhat test above
  one uniform threshold.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.AdjacentCompactMatrix.exists_integrable_realTwist_bound`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
