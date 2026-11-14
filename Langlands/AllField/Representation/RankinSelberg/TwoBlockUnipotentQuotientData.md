# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The two-block unipotent quotient and its radical fiber average**

JPSS (1983), Section 4.6, printed pages 411-412: the first unfolding passes from
equation (4), an iterated integral over `N_r \ G_r^m` and the complementary upper
radical, to the integral over `N_(t_1,t_2) \ G_r^m`, where `N_(t_1,t_2)` is the group
(5) of block diagonal matrices `diag(n_1, n_2)` with `n_i` upper unipotent.

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, this module
constructs that subgroup `H` of `GL_(t+1)`, the actual left quotient `H \ GL_(t+1)`
with the projection to `N \ GL_(t+1)`, the radical fiber map
`(x, g) ↦ [u(x) g]_H`, its unweighted fiber integral, the descended radical average on
`N \ GL_(t+1)` and the determinant slices of `H \ GL_(t+1)`. No integrability,
quotient-measure, or Fubini statement is asserted.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.continuous_projection` (theorem): The projection `H \ G → N \ G` is continuous for the quotient topologies.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.continuous_fiberPoint` (theorem): The radical fiber map is jointly continuous in `(x, g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.fiberIntegral` (def): The unweighted radical fiber integral `g ↦ ∫ f([u(x) g]_H) dμ(x)`, the ordinary total
  Bochner integral against the supplied measure on the rectangle.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.fiberIntegral_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.fiberIntegral_upperUnipotent_mul` (theorem): Left `N`-invariance of the fiber integral, for every Borel additive Haar measure on the
  rectangle and every scalar function, without any integrability hypothesis.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.radicalAverage` (def): The radical average on the actual quotient `N \ GL_(t+1)`: the actual descent of the
  left-`N`-invariant fiber integral. No coset representative is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.radicalAverage_mk` (theorem): Representative evaluation of the radical average.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice` (def): The determinant slice of `H \ GL_(t+1)`: the preimage under `projection` of the published
  slice `N \ G^k = {ord(det g) = k}`.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.mk_mem_determinantSlice` (theorem): Representative condition `ord(det g) = k`, for the published normalized order.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.isClopen_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.measurableSet_determinantSlice` (theorem): Every slice is measurable for any Borel structure on the intermediate quotient.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.BlockUnipotents`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.mem_upperUnipotent_of_blocks`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.upperRadical_mem_upperUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.determinant_eq_one_of_mem_upperUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_apply`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_index_same`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_index_zero_one`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_index_one_zero`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_injective`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_mem_upperUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.mem_blockUnipotent_iff`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockEmbedding_mem`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotent_le_upperUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.determinant_blockEmbedding`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.determinant_eq_one_of_mem_blockUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.unipotentLevi_blockEmbedding`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.mem_blockUnipotent_iff_corner`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotentEquiv`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotentEquiv_apply_val`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotentEquiv_symm_apply_val`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotentEquiv_symm_apply_apply`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.upperRadical_mul_upperUnipotent_mul`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.continuous_blockEmbedding`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.continuous_unipotentLevi`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotentHomeomorph`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.blockUnipotentHomeomorph_toMulEquiv`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.isClosed_blockUnipotent`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.canonicalBlockUnipotentHomeomorph`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.continuous_blockUnipotentEquiv`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.continuous_blockUnipotentEquiv_symm`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.isClosed_blockUnipotent_canonical`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.mk_mul_of_mem`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.BlockQuotient`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.projection`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.projection_mk`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.projection_surjective`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.fiberPoint`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.fiberPoint_def`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.projection_fiberPoint`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.fiberPoint_upperUnipotent_mul`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.t2Space_blockQuotient`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.projection_rightTranslate`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.fiberPoint_mul`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.fiberIntegral_mul`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.radicalAverage_rightTranslate`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.mem_determinantSlice`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.determinantOrder_projection_fiberPoint`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.fiberPoint_mem_determinantSlice_iff`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.pairwise_disjoint_determinantSlice`, `Langlands.RankinSelberg.TwoBlockUnipotentQuotient.iUnion_determinantSlice`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
