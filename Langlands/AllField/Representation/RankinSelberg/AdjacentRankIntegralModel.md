# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPSS Section 6.1: the special `(r+1,1)` tensor integral model**

The raw scalar integral of JPSS Section 6.1, formula (8), in ambient rank `r + 2`
with lower blocks `(r + 1, 1)`. Test vectors are finite tensors of rectangular
Schwartz functions with vectors of the actual Whittaker coefficient image, and
`ρ₀` acts on the Schwartz factor only. The integral is the totalized Bochner
integral for a supplied measure; no convergence or model membership is asserted.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceProof`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.AdjacentRankModelConverges` (def): Convergence for the shared Haar measure on the inner `GL_(r+1)`.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral` (def): The raw formula (8) integral for the shared Haar measure on the inner `GL_(r+1)`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.adjacentRankTestSpace`, `Langlands.RankinSelberg.adjacentRankTestBilinear`, `Langlands.RankinSelberg.adjacentRankTestEvaluation`, `Langlands.RankinSelberg.adjacentRankTestEvaluation_tmul`, `Langlands.RankinSelberg.adjacentRankTestEvaluation_zero`, `Langlands.RankinSelberg.adjacentRankTestEvaluation_add`, `Langlands.RankinSelberg.adjacentRankTestEvaluation_smul`, `Langlands.RankinSelberg.adjacentRankTestEvaluation_sum`, `Langlands.RankinSelberg.adjacentRankTestSpace_exists_sum_tmul`, `Langlands.RankinSelberg.adjacentRankTestSpace_induction`, `Langlands.RankinSelberg.adjacentRankTestEvaluation_sum_tmul`, `Langlands.RankinSelberg.adjacentRankEpsilon`, `Langlands.RankinSelberg.adjacentRankKernelMatrix`, `Langlands.RankinSelberg.inverseTranspose_mulVec_adjacentRankEpsilon`, `Langlands.RankinSelberg.adjacentRankKernelMatrix_castSucc`, `Langlands.RankinSelberg.adjacentRankKernelMatrix_last`, `Langlands.RankinSelberg.rectangularFirstColumns_adjacentRankKernelMatrix`, `Langlands.RankinSelberg.rectangularLastColumn_adjacentRankKernelMatrix`, `Langlands.RankinSelberg.adjacentRankKernelMatrix_rankZero`, `Langlands.RankinSelberg.adjacentRankRho0`, `Langlands.RankinSelberg.adjacentRankRho0_apply`, `Langlands.RankinSelberg.adjacentRankRho0_tmul`, `Langlands.RankinSelberg.adjacentRankRho0_one`, `Langlands.RankinSelberg.adjacentRankRho0_mul`, `Langlands.RankinSelberg.adjacentRankModelIntegrand`, `Langlands.RankinSelberg.AdjacentRankModelConverges`, `Langlands.RankinSelberg.adjacentRankModelIntegral`, `Langlands.RankinSelberg.adjacentRankModelIntegrand_zero`, `Langlands.RankinSelberg.adjacentRankModelIntegrand_add`, `Langlands.RankinSelberg.adjacentRankModelIntegrand_smul`, `Langlands.RankinSelberg.adjacentRankModelIntegrand_sum`, `Langlands.RankinSelberg.adjacentRankModelIntegrand_tmul`, `Langlands.RankinSelberg.adjacentRankModelConverges_zero`, `Langlands.RankinSelberg.AdjacentRankModelConverges.add`, `Langlands.RankinSelberg.AdjacentRankModelConverges.smul`, `Langlands.RankinSelberg.adjacentRankModelConverges_sum`, `Langlands.RankinSelberg.adjacentRankModelIntegral_zero`, `Langlands.RankinSelberg.adjacentRankModelIntegral_add`, `Langlands.RankinSelberg.adjacentRankModelIntegral_smul`, `Langlands.RankinSelberg.adjacentRankModelIntegral_sum`, `Langlands.RankinSelberg.adjacentRankModelIntegral_tmul`, `Langlands.RankinSelberg.Padic.adjacentRankModelIntegrand`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
