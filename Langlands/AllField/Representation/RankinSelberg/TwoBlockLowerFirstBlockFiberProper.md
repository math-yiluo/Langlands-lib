# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact finiteness of the actual lower mixed fiber kernels**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockFiberProper`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberKernels`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.rightRadicalCoord` (def): The right radical coordinate of a lower mixed matrix.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_rightRadicalCoord` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.rightRadicalCoord_mixed_mul_radical` (theorem): The coordinate recovers the radical after any diagonal mixed factor.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint_isCompact_preimage` (theorem): Radical fibers have compact preimages of compact sets in the mixed quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedFirstQuotient` (def): The small quotient of the first diagonal coordinate.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_lowerMixedFirstQuotient` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedFirstQuotient_lower_mul` (theorem): Multiplication from the lower unipotent subgroup leaves the first quotient unchanged.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint_slice_isCompact_preimage` (theorem): First-block fibers restricted to one determinant slice have compact preimages.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalKernel_compact_ne_top` (theorem): Every radical kernel measure is finite on compact sets.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalKernel_isSFinite` (theorem): Compact finiteness on a common countable compact cover gives radical kernel s-finiteness.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockKernel_compact_ne_top` (theorem): Every first-block slice kernel measure is finite on compact sets.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockKernel_isSFinite` (theorem): Compact finiteness on a common countable compact cover gives first-block kernel s-finiteness.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.quotientFiber_isCompact_preimage_of_coordinate`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
