# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJacquetLimit`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLimit` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetLimit`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetLimit` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Pointwise model convergence for norm-bounded full-rank Schwartz approximations.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetIntegrability`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.tendsto_doubleIntegral` (theorem): Dominated convergence on the genuine row-times-matrix measure, followed by
  Fubini, for every ambient translate of the whole Schwartz test.
- `Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.tendsto_modelIntegral` (theorem): The actual model integrals of the partial Fourier transforms converge
  pointwise, with the original threshold and supplied Haar normalization.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.realTwistCoefficientMap` (def): All coefficients of the one identity Jacquet integral as a scalar linear map.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.realTwistCoefficientMap_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.realTwistCoefficientMap_coefficient` (theorem): This linear map consists of coefficients of one fixed identity integral.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.adjacentRankFullRank_doubleKernel`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
