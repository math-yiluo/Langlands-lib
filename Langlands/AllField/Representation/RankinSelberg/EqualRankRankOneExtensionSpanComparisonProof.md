# All-field port of `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof`

`Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Equal-rank rank-one extension Laurent-span comparison: proof**

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanTransfer`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`
- `Langlands.AllField.Representation.Whittaker.CoefficientRightStabilizer`
- `Langlands.AllField.Representation.Whittaker.TwoBlockExtensionAssemblyProof`

## Declarations

- `Langlands.AllField.RankinSelberg.half_mul_determinantWeight` (theorem): The half power of the determinant combines with the corank-one weight.
- `Langlands.AllField.RankinSelberg.exists_inverseWhittaker_twoBlockExtension` (theorem): JPSS Proposition 9.1 with a rank-one first block, read in the
  inverse-character model of the induction of the unlifted pair `(χ, σ₁)`.
- `Langlands.AllField.RankinSelberg.equalRankSpanComparison_core` (theorem): The span comparison at a general induced rank `m = t + 1`, from the
  last-row reduction, the zero-row cutoff and a supplied extension of inverse
  Whittaker functions of `σ₁` to inverse Whittaker functions of `I`.
- `Langlands.AllField.RankinSelberg.equalRankRankOneExtensionSpanComparison_of` (theorem): The span comparison from JPSS Proposition 9.1 and the last-row reduction
  `equalRankLastRowReduction`.
- `Langlands.AllField.RankinSelberg.equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity` (theorem): The span comparison from p-adic row Fourier surjectivity, through the
  published conditional proof `Langlands.AllField.Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity`
  of JPSS Proposition 9.1.
- `Langlands.AllField.RankinSelberg.equalRankRankOneExtensionSpanComparison` (theorem): The equal-rank rank-one extension Laurent-span comparison, from the
  published proof `Langlands.AllField.HarmonicAnalysis.padicRowFourierSurjectivity`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.exists_mem_coefficientModel_of_character_eq`, `Langlands.RankinSelberg.exists_inverseWhittakerSet_of_scale_neg_one`, `Langlands.RankinSelberg.exists_whittakerSet_scale_neg_one`, `Langlands.RankinSelberg.corankOneRestrict`, `Langlands.RankinSelberg.corankOneRestrict_val`, `Langlands.RankinSelberg.prod_dirac_eq_map`, `Langlands.RankinSelberg.corankOneConverges_of_unequalRankConverges_zero_zero`, `Langlands.RankinSelberg.pairFamilyEquivRight`, `Langlands.RankinSelberg.conjULiftEquiv`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
