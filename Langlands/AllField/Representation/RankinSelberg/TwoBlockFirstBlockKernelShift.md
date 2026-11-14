# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Determinant transport for the first-block fiber kernel**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockSliceShift`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.map_restrict_smallSlice_of_ord` (theorem): Right translation carries the zero small slice to the prescribed slice exactly.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.exists_determinantOrder` (theorem): Every integer occurs as the determinant order of a positive-rank matrix.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberPoint_firstBlockEmbedding_mul` (theorem): Arbitrary first-block multiplication of the base is right translation of the fiber.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_eq_zero_shift` (theorem): The k-th fiber kernel is the zero kernel evaluated at the shifted outer point.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice` (theorem): Kernel composition transports the inner k slice to the outer k slice.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberKernel_comp_zeroSlice_eq` (theorem): The all-slices conclusion follows from zero-kernel disintegration on each outer slice.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.FirstBlockKernelShiftStatement`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockKernelShift`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
