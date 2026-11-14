# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The first-block slice tower of the lower mixed quotient**

For every determinant order `k`, the unweighted first-block slice kernel composed with
the zero slice of a compatible lower mixed quotient measure is, after the density
`q^(-k b)`, the slice `k` of the compatible lower quotient measure.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.ambientSlice` (def): The ambient determinant slice `G^k = {g | ord(det g) = k}` of `GL_n`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.isClopen_ambientSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.ord_determinant_mul_of_mem` (theorem): Left multiplication by a norm-one matrix preserves the determinant order.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.quotientAverageReal_indicator_ambientSlice` (theorem): Averaging over a subgroup of `GL_n^0` commutes with cutting by an ambient slice.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_mul_right_of_ord` (theorem): Right multiplication by `v` with `ord(det v) = k` scales every rectangular additive
  Haar on `b × a` matrices by `q^(k b)`; the density `q^(-k b)` compensates it.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.small_orbitKernel_comp_slice` (theorem): The small orbital measure restricted to slice `k` is the left translate by `z` of the
  norm-one Haar, for any `z` with `ord(det z) = k`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_firstBlockFiberPoint_quotientAverageReal` (theorem): **Per-point slice identity.** Over the small slice `k`, the density times the integral
  of the `H⁻` averages at the first-block fiber points of `g` is the lower mixed average at
  `g` of the left translate `x ↦ f(I(z) x)`, for any `z` with `ord(det z) = k`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_firstBlockKernel_comp_quotientAverageReal` (theorem): The composite first-block slice kernel integrates `H⁻` averages to the lower mixed
  averages of the left translate `x ↦ f(I(z) x)`, after the density, for every outer measure.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.eq_of_lintegral_lowerQuotientAverageReal` (theorem): Two measures on `H⁻ \ G` that integrate every nonnegative `H⁻` average to the same
  finite value coincide.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockKernel_comp_zeroSlice` (theorem): **First-block slice tower.** For compatible measures and every determinant order `k`,
  the density `q^(-k b)` times the first-block slice-`k` kernel composed with the zero slice
  of the lower mixed quotient measure is the slice `k` of the lower quotient measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.leviEmbedding_mul_lowerRadical_mul_firstBlockEmbedding`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockEmbedding_mul_leviEmbedding`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.FirstBlockSliceTowerStatement`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockSliceTower`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
