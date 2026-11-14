# All-field port of `Langlands.Group.GL.LowerBlockQuotientGeometryProof`

`Langlands.AllField.Group.GL.LowerBlockQuotientGeometryProof` is the all-field port of the Library module `Langlands.Group.GL.LowerBlockQuotientGeometryProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Group.GL.LowerBlockQuotientGeometryProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Geometry of the lower-block quotient chart**

The published chart `([g], x, h) ↦ [[[g,0],[x,h]]]` from `N_a \ GL_a × M_{d×a} × B⁻_d`
to `N_{a+d} \ GL_{a+d}` is an open embedding, is Borel measurable, and has conull
range for every compatible quotient measure. Openness: after right translation by
`diag(g₀, 1)`, the chart restricted to the big-cell parameters `([b g₀], x g₀, h)`
is the composite of block coordinates `B⁻_a × M × B⁻_d ≃ₜ B⁻_{a+d}` with the open
cell `B⁻_{a+d} → N_{a+d} \ GL_{a+d}`. These parameter sets cover. Conullness: the
range contains every coset of a lower triangular matrix, and these cosets are
conull.

## Imports from the port

- `Langlands.AllField.Group.GL.LowerBlockQuotientGeometryStatement`
- `Langlands.AllField.Group.GL.LowerTriangularBigCellConull`
- `Langlands.AllField.Group.GL.LowerTriangularQuotientCell`

## Declarations

- `Langlands.AllField.GeneralLinear.continuous_lowerBlockCellParameters` (theorem): The translated big-cell parameter map is continuous.
- `Langlands.AllField.GeneralLinear.isOpenMap_lowerBlockQuotientChart_comp_cellParameters` (theorem): On translated big-cell parameters the chart is an open map.
- `Langlands.AllField.GeneralLinear.isOpenMap_lowerBlockQuotientChart` (theorem): The chart is an open map.
- `Langlands.AllField.GeneralLinear.isOpenEmbedding_lowerBlockQuotientChart` (theorem): The chart is an open embedding.
- `Langlands.AllField.GeneralLinear.measurable_lowerBlockQuotientChart` (theorem): The chart is measurable for the Borel structures on the quotients, the
  field and the lower triangular group, and the induced product structures.
- `Langlands.AllField.GeneralLinear.lowerBlockQuotientChart_range_compl_null` (theorem): The range of the chart is conull for every compatible quotient measure: it
  contains the conull set of cosets of lower triangular matrices.
- `Langlands.AllField.RankinSelberg.lowerBlockQuotientGeometry` (theorem): Proof of `LowerBlockQuotientGeometryStatement`: the actual lower-block chart
  is an open measurable embedding with conull range.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.lowerBlockCellParameters`, `Langlands.GeneralLinear.lowerBlockQuotientChart_lowerBlockCellParameters`, `Langlands.GeneralLinear.exists_lowerBlockCellParameters_eq`, `Langlands.GeneralLinear.mk_lowerTriangular_mem_range_lowerBlockQuotientChart`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
