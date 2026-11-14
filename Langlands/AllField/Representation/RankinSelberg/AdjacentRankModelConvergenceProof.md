# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unconditional convergence of the adjacent-rank tensor integral**

The pure-tensor scalar integrand has compact support on the inner general
linear group. The first columns give a compact matrix bound; the last column
and smooth Whittaker simple-root support bound the inverse determinant.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankSliceSupportProof`
- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`

## Declarations

- `Langlands.AllField.RankinSelberg.continuous_adjacentRankKernelMatrix` (theorem): The rectangular kernel is continuous, including its inverse-row column.
- `Langlands.AllField.RankinSelberg.exists_adjacentRank_lastColumn_bound` (theorem): The Schwartz factor bounds the last row of the inverse matrix on its support.
- `Langlands.AllField.RankinSelberg.adjacentRankPure_hasCompactSupport` (theorem): The product of the kernel Schwartz factor and any smooth Whittaker model
  coefficient has compact support on the actual inner general linear group.
- `Langlands.AllField.RankinSelberg.continuous_adjacentRank_determinantWeight` (theorem): The canonical determinant weight is continuous on GL for every complex
  exponent, since its base is strictly positive.
- `Langlands.AllField.RankinSelberg.adjacentRankModelConverges_tmul_of_isSmooth` (theorem): A pure tensor gives an actually integrable formula (8) integrand, for every
  ambient element and every continuous quasicharacter.
- `Langlands.AllField.RankinSelberg.adjacentRankModelConvergence` (theorem): JPSS Section 6.1, formula (8), converges unconditionally for all test tensors
  and all data in the published adjacent-rank model statement.
