# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Assembly from a single-vector block-zero equation**

The actual constant second model vector can be absorbed into the first vector,
simultaneously in the original and Weyl-transformed complementary integrals.
The analytic block-zero equation remains an explicit input.

## Imports from the port

- `Langlands.AllField.LocalFactor.ResidueReflection`
- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange`
- `Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType`
- `Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero`
- `Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankGammaPropagationProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`
- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOne_blockZero_exists_ne_zero` (theorem): Unit membership for actual unequal-rank integrals supplies a nonzero
  block-zero continuation for the supplied first model and canonical second model.
- `Langlands.AllField.RankinSelberg.rankOneGammaFactor_of_blockZero_one` (theorem): A block-zero equation for the canonical second vector supplies the full
  symmetric gamma relation, with the same multiplier, all blocks, all compatible
  quotient measures and all pairs of nonzero Whittaker functionals.
- `Langlands.AllField.RankinSelberg.rankOneGammaFactor_of_normalized_blockZero_one` (theorem): The normalized equation for the same actual block-zero pair yields the
  specified rational gamma expression on its full reduced-denominator domain.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankOneTrivialModelOne`, `Langlands.RankinSelberg.rankOneTrivialModelOne_apply`, `Langlands.RankinSelberg.rankOneTrivialModel_eq_smul_one`, `Langlands.RankinSelberg.unequalRankIntegralAt_rankOne_absorb`, `Langlands.RankinSelberg.dualUnequalRankModelIntegralAt_rankOne_absorb`, `Langlands.RankinSelberg.unequalRankBlockZeroGammaEquation_rankOne_of_one`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
