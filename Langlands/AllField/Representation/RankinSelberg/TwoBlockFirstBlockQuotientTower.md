# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.lintegral_fiberPoint_quotientAverageReal` (theorem): Integrating the block average over the small zero slice gives the exact mixed average.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.lintegral_comp_quotientAverageReal` (theorem): The composite zero-slice fiber measure integrates block averages to mixed averages.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_zero_comp` (theorem): The normalized full tower has coefficient exactly one.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_zero_comp_restrict` (theorem): The zero small slice preserves the determinant slice of the mixed base.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.NormalizedTowerStatement` (abbrev): Exact full and same-slice composition for the zero small-slice kernel.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normalized_tower` (theorem): Compatible measures satisfy the normalized full tower and all its same-slice restrictions.
