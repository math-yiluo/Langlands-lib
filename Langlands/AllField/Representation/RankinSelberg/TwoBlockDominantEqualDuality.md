# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualDuality` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual duality at the equal-rank boundary**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualKernel`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierAnalytic`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.negatedSelfDualHaar` (def): The supplied self-dual measure, with its inverse-character certificate.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.negatedSelfDualHaar_val` (theorem).
- `Langlands.AllField.RankinSelberg.DominantRankTransport.determinantComplexPower_inverseTranspose` (theorem): Inverse transpose negates every complex determinant-power exponent.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.reversedDual_oppositeTwistBlocks` (theorem): Complete reversal and inverse transpose preserve the opposite-twist parameter.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalLowerGroupIntegrand_reversedDual` (theorem): The fixed section equivalence discharges the scalar-section premise in
  the published Fourier comparison.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalLowerIntegrand_reversedDual` (theorem): The pointwise comparison descends along the actual lower duality.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.EqualLowerFourierCoefficientLaw` (def): The actual equal-rank lower coefficient law, including integrability and
  the raw-norm integral, for the supplied standard quotient measure.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalLowerFourierCoefficientLaw` (theorem): The actual section equivalence and published supplied-measure transport
  prove the coefficient law, with no scalar-section comparison premise.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.fourierIntegral_scale_neg_one`, `Langlands.HarmonicAnalysis.IsSelfDual.scale_neg_one`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
