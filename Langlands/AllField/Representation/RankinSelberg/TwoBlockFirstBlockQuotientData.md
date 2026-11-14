# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The first-block norm-one quotient and the first-block slice average**

JPSS (1983), Section 4.6, printed page 412, equation (6): for `r = t_1 + t_2`,

`∫_{N_(t_1,t_2) \ G_r^m} f(g) dg =
  ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a`.

For two blocks of sizes `a = m 0 + 1` and `b = m 1 + 1` of total rank `t + 1`, this module
constructs the actual data of this displayed formula: the first-block embedding
`u ↦ diag(u, 1_b)`, the subgroup `L = diag(GL_a^0, N_b) = G_(t_1)^0 N_(t_1,t_2)` with its
quotient `L \ GL_(t+1)` and determinant slices, the fiber map
`([u], g) ↦ [diag(u, 1) g]_H` from the small quotient `N_a \ GL_a` to
`H \ GL_(t+1)` with `H = N_(t_1,t_2)`, the inner slice integral and its descent to
`L \ GL_(t+1)`. No integrability, quotient-measure, or Fubini statement is asserted.

## Imports from the port

- `Langlands.AllField.Representation.Jacquet.ParabolicSupplement`
- `Langlands.AllField.Representation.Parabolic.FlattenedRefinementModulusCalculation`
- `Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneSubgroup` (abbrev): The norm-one subgroup `GL_n^0 = {u | |det u| = 1}`, the kernel of the published
  determinant norm for the canonical realization.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mem_normOneSubgroup_iff` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mem_normOneSubgroup_iff_normalizedAbs` (theorem): Norm one is the condition `|det u| = 1` for the normalized absolute value.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.ord_determinant_eq_zero` (theorem): A norm-one matrix has determinant of order zero.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding` (def): The embedding `(u, n) ↦ diag(u, n)` of `GL_(m 0 + 1)^0 × N_(m 1 + 1)` into
  `GL_(t+1)`, through the published Levi embedding of `succBlockShape m h`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_apply` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_index_zero_zero` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_index_zero_one` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_index_one_zero` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_index_one_one` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinant_mixedEmbedding` (theorem): `det diag(u, n) = det u`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup` (def): The subgroup `L = G_(t_1)^0 N_(t_1,t_2) = diag(GL_(m 0 + 1)^0, N_(m 1 + 1))` of JPSS
  (4.6), (6): the actual image of `mixedEmbedding`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_mem` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mem_mixedSubgroup_iff` (theorem): Intrinsic block-entry description of `L`: both off-diagonal blocks vanish, the first
  diagonal block has determinant of normalized absolute value one (so it is invertible), and
  the second diagonal block is upper unipotent.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mem_mixedSubgroup_iff_determinantNorm` (theorem): Equivalent intrinsic description with the determinant norm of the whole matrix: this
  form exhibits `L` as an intersection of closed conditions.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup_le_normOneSubgroup` (theorem): `L ≤ ker |det|`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.blockUnipotent_le_mixedSubgroup` (theorem): `H = N_(t_1,t_2) ≤ L`: the first block of `H` is upper unipotent, hence of norm one.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup_le_parabolic` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedCoordinates` (def): The diagonal blocks of an element of `L`, by the published Levi projection.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedCoordinates_mixedEmbedding` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_mixedCoordinates` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupEquiv` (def): The multiplicative equivalence of `GL_(m 0 + 1)^0 × N_(m 1 + 1)` with `L`; the inverse
  extracts the diagonal blocks.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupEquiv_apply_val` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupHomeomorph` (def): The equivalence `GL_(m 0 + 1)^0 × N_(m 1 + 1) ≃ L` is a homeomorphism for the canonical
  p-adic topology.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.isClosed_mixedSubgroup` (theorem): `L` is closed: it is cut out by the vanishing of the off-diagonal blocks, the
  upper-unipotent conditions on the second block, and the open, hence closed, kernel of
  `|det|`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient` (abbrev): The actual left quotient `L \ GL_(t+1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder` (def): The quotient determinant order `[g]_L ↦ ord(det g)`; it is well defined because every
  element of `L` has determinant of order zero.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder_mk` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_determinantOrder` (theorem): The determinant order is continuous into the discrete integers.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice` (def): The determinant slice `L \ G^k = {q | ord(det q) = k}` of the mixed quotient. The
  outer domain of JPSS (4.6), (6) is the slice `k = 0`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mem_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.isClopen_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.measurableSet_determinantSlice` (theorem): Every slice is measurable for any Borel structure on the mixed quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_fiberPoint` (theorem): The fiber map is jointly continuous in `(q, g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberPoint_mem_determinantSlice_iff` (theorem): `fiberPoint q g` lies in the published slice `H \ G^k` exactly when
  `ord(det q) + ord(det g) = k`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberPoint_mixedEmbedding_mul` (theorem): Change of fiber: left multiplication of the base point by `diag(u, n) ∈ L` is right
  multiplication of the small quotient by `u`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.NormOneRightInvariant` (def): Right translation of the small quotient by every norm-one `u` preserves the measure,
  for the Borel structure of the quotient topology.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible` (theorem): A compatible quotient measure on the small full-unipotent quotient, in the sense of the
  published `QuotientIntegration.IsCompatible`, is invariant under all right translations,
  in particular under those by norm-one matrices.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberIntegral` (def): The inner integral of JPSS (4.6), (6): the total Bochner integral
  `∫_{N_a \ GL_a^k} f(fiberPoint q g) dμA(q)` over the published small slice, for the supplied
  measure on the Borel structure of the small quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberIntegral_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberIntegral_mixedEmbedding_mul` (theorem): Left invariance under `diag(u, n) ∈ L`, without any integrability hypothesis: right
  translation by `u` preserves `μA` and, since `ord(det u) = 0`, the small slice.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.fiberIntegral_mixedSubgroup_mul` (theorem): Left invariance under every element of `L`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage` (def): The first-block average on the actual quotient `L \ GL_(t+1)`: the actual descent of
  the left-`L`-invariant inner slice integral. No coset representative is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_mk` (theorem): Representative evaluation of the first-block average.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.blockPair`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.blockPair_apply_zero`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.blockPair_apply_one`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.blockPair_eta`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.determinant_leviEmbedding_blockPair`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.leviEmbedding_blockPair_mem_blockUnipotent`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_apply`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_index_zero_zero`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_index_zero_one`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_index_one_zero`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_index_one_one`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_injective`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.determinant_firstBlockEmbedding`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_mem_blockUnipotent`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockEmbedding_mul_leviEmbedding_blockPair`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.mem_parabolic_of_index_one_zero`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.leviEmbedding_leviProjection_of_blocks`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.det_firstBlock_eq`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_blockPair`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_firstBlockEmbedding`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.last_eq_index_one`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.lastRow_firstBlockEmbedding_mul`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.fiberPoint`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.fiberPoint_mk`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.mixedEmbedding_injective`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.det_firstBlock_ne_zero`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupEquiv_symm_apply_fst`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupEquiv_symm_apply_snd`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupHomeomorph_toMulEquiv`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.projection`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.projection_mk`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.projection_surjective`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.continuous_projection`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.projection_rightTranslate`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.t2Space_mixedQuotient`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.mk_mem_determinantSlice`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder_projection_mk`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.projection_preimage_determinantSlice`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.determinantOrder_rightTranslate`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.rightTranslate_mem_determinantSlice`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.fiberPoint_mul`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.fiberIntegral_mul`, `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_rightTranslate`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
