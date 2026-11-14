# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantBlockSupport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform rectangular support in a leading diagonal block**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankIwasawaSupportProof`
- `Langlands.AllField.Representation.Whittaker.TwoBlockJacquetCovarianceProof`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.blockSum_mem_integralOpen` (theorem): The actual block sum preserves integrality of both matrices and inverses.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_coefficient_blockSum_rootBounded` (theorem): Nonvanishing of a smooth ambient coefficient gives root bounds in
  independent Iwasawa decompositions of both actual diagonal blocks.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.normalizedAbs_ratios_of_rootBounded` (theorem): Integer adjacent root bounds imply the precise normalized ratio bound.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.IsBlockSumRectangularSupport` (def): A compact rectangle support set uniform in the leading group coordinate,
  the other invertible diagonal block and the right integral factor.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_blockSum_rectangular_support` (theorem): A nonzero smooth ambient coefficient has compact rectangular support in a
  leading unequal-rank block, uniformly in the entire other invertible block
  and the supplied right integral factor.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.blockSum_torus`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.rootBounded_append_left`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.rootBounded_append_right`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
