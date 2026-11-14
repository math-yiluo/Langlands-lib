# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform box extraction at arbitrary additive conductor**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxVolume`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneBox.mul_mem_box_of_le` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.mul_mem_box_iff_of_le` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotentBox_eq_entry_preimage` (theorem): In actual strict upper-entry coordinates the box is a finite product of
  compact scalar lattices, for every integer first-row level.
- `Langlands.AllField.RankinSelberg.RankOneBox.isCompact_unipotentBox` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotentHaar_unipotentBox_lt_top_all` (theorem): Finiteness holds at arbitrary conductor, including positive lattice levels.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalLevel_firstRow` (theorem): The principal-level first row fits exactly the choice A = q + a.
- `Langlands.AllField.RankinSelberg.RankOneBox.cutoffUnipotent_mem_principalLevel` (theorem): The small transvection belongs to the same principal subgroup as its scalar.
- `Langlands.AllField.RankinSelberg.RankOneBox.rankOne_support_of_principalLevel` (theorem): Right principal-level invariance gives a support bound independent of H.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxCoefficient_mul_principalLevel` (theorem): Right invariance of the box coefficient uses only the inequality q ≤ A.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxCoefficient_point` (theorem): Pointwise extraction applies to an arbitrary left-equivariant coefficient,
  without a representation or a selected vector.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxExtractionConstant` (def): The positive extraction constant depends only on the box and its rank.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxExtractionConstant_pos` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.boxCoefficient_extraction_of_principalLevel` (theorem): One fixed box extracts every continuous, equivariant, principal-level
  invariant coefficient, with equivalence of genuine absolute convergence.
- `Langlands.AllField.RankinSelberg.RankOneBox.uniform_box_extraction` (theorem): At additive conductor c, the single box with A = c + a and q = c works
  uniformly for every coefficient fixed by the same positive principal level.
