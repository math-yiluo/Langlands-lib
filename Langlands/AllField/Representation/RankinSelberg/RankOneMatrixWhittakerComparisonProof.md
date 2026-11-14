# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the rank-one JPSS comparison `I₁ = I₃`**

The case `n = 0` is `rankOneMatrixWhittakerComparison_zero`. For `n = m + 1` both
value sets equal the reduced `GL₁` value set `rankOneModelValues`: the left one by
`characterZetaValues_one_succ_eq`, the right one by the two inclusions
`RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues` and
`rankOneModelValues_subset_whittakerRationalValues`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneMatrixWhittakerComparison_of_positive` (theorem): The comparison statement follows from the positive-rank identification of the
  matrix–Whittaker values with the reduced `GL₁` values.
- `Langlands.AllField.RankinSelberg.whittakerRationalValues_eq_rankOneModelValues` (theorem): The positive-rank identification of the matrix–Whittaker values with the reduced
  `GL₁` values.
- `Langlands.AllField.RankinSelberg.rankOneMatrixWhittakerComparison` (theorem): **The rank-one JPSS comparison `I₁ = I₃`.**
