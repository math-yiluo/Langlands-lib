# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantEndpointBounds`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEndpointBounds` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantEndpointBounds`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantEndpointBounds` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Endpoint bounds in a leading unequal-rank block**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantLeviSupport`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.iwasawa_principal_suffix_minor_bound` (theorem): A principal suffix minor is bounded by the Iwasawa diagonal on that suffix.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.unequalRankMatrix_last_entry_bound` (theorem): A bounded adjacent Iwasawa ratio and the terminal identity row bound the
  last entry of the original leading group block.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.IsBlockSumLastEntryBound` (def): An endpoint entry bound uniform in the rectangle, the other invertible
  diagonal block and the right integral factor.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_blockSum_last_entry_bound` (theorem): A smooth ambient coefficient uniformly bounds the leading endpoint entry.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_reindex_blockSum_last_entry_bound` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.IsLeviSecondEndpointBound` (def): A bound for the actual second Levi block's terminal diagonal entry whenever
  the coefficient at the actual dominant matrix is nonzero.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_levi_second_endpoint_bound` (theorem): The actual second endpoint bound holds for every smooth ambient coefficient.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.unequalRankMatrix_last_entry_minor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
