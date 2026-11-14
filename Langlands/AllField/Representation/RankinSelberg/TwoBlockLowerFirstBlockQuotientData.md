# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The lower mixed quotient and its two fiber averages**

Derived data for JPSS (1983), Section 4.9, equations (2) and (8).

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup` (def): The actual lower mixed subgroup: `R(Z) diag(a0,n)` with `|det a0| = 1` and
  `n` upper unipotent. The lower-left block is unrestricted.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_mem` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixed_decomposition` (theorem): Elimination into the actual lower radical and the published mixed embedding.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.mem_lowerMixedSubgroup_iff` (theorem): Intrinsic block criterion, using actual entries and the normalized absolute value
  of the first diagonal determinant. Invertibility is supplied by the opposite Levi projection.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.mixedSubgroup_le_lowerMixedSubgroup` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerBlockUnipotent_le_lowerMixedSubgroup` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup_le_oppositeParabolic` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup_le_normOneSubgroup` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedDiagonal` (def): The first diagonal block is invertible, with its actual inverse extracted by the
  opposite Levi projection; its determinant has absolute value one.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedDiagonal_fst_val` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedDiagonal_snd_val` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedCoordinates` (def): Coordinates `(X * a0⁻¹, (a0,n))` of the actual block matrix `[[a0,0],[X,n]]`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedDiagonal_lowerProduct` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedCoordinates_lowerProduct` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_lowerMixedCoordinates` (theorem): Reconstructing from the coordinates returns the original matrix.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv` (def): The coordinate equivalence, before topology. Its domain is given the semidirect
  multiplication stated below, rather than the product group multiplication.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv_apply_val` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupHomeomorph` (def): The coordinate equivalence is a homeomorphism in the canonical topology.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.isClosed_lowerMixedSubgroup` (theorem): Closedness follows from the actual upper-right block, first determinant and
  upper-unipotent second block conditions.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv_symm_apply_fst` (theorem): The first inverse diagonal coordinate is the actual first entry block.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv_mul` (theorem): Coordinate multiplication is semidirect: `Z + n Z2 a0⁻¹` on the rectangle.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.LowerMixedQuotient` (abbrev): The actual left quotient by the lower mixed subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromMixed` (def): Projection from the published diagonal mixed quotient, by actual quotient descent.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromLower` (def): Projection from the published lower unipotent quotient, by actual quotient descent.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromMixed_mk` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromLower_mk` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_projectionFromMixed` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_projectionFromLower` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder` (def): The determinant order descends because the lower mixed subgroup lies in `GL^0`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder_mk` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_determinantOrder` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice` (def): Integer determinant slices. The source's `Lminus \ G^0` is precisely slice zero.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.mk_mem_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.isClopen_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.measurableSet_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder_projectionFromMixed` (theorem): Both projections preserve the determinant order.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder_projectionFromLower` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromMixed_preimage_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromLower_preimage_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint` (def): The rectangular fiber map `(Z, g) ↦ [R(Z) g]_M` into the published mixed quotient
  `M \ G`, `M = diag(GL_a^0, N_b)`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_radicalFiberPoint` (theorem): The rectangular fiber map is jointly continuous in `(Z, g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder_radicalFiberPoint` (theorem): Since `det R(Z) = 1`, the fiber point has the determinant order of `g`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint_mem_determinantSlice_iff` (theorem): The fiber point lies in the published slice `M \ G^k` exactly when `ord(det g) = k`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalChange` (def): The affine change of rectangular coordinates `Z ↦ n⁻¹ (Z + Z0) a0` attached to
  `l = R(Z0) D(a0, n)`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalChange_apply` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint_lowerRadical_mixedEmbedding_mul` (theorem): Representative change: for `l = R(Z0) D(a0, n)`,
  `radicalFiberPoint Z (l g) = radicalFiberPoint (n⁻¹ (Z + Z0) a0) g`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalChangeHomeomorph` (def): The affine change is a homeomorphism of the rectangle.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalChangeHomeomorph_apply` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.measurePreserving_radicalChange` (theorem): The affine change `Z ↦ n⁻¹ (Z + Z0) a0` preserves every Borel additive Haar measure on
  the rectangle: its linear part has both determinant norms one
  (`padicRectangularHaarScaling`), and the translation part preserves Haar measure.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.integral_comp_radicalChange` (theorem): Integrals over the rectangle are invariant under the affine change, with no
  integrability hypothesis.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberIntegral` (def): The rectangular fiber integral `g ↦ ∫ f([R(Z) g]_M) dμR(Z)`, the ordinary total Bochner
  integral against the supplied measure on the rectangle.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberIntegral_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberIntegral_lowerRadical_mixedEmbedding_mul` (theorem): Left invariance under `l = R(Z0) D(a0, n)`, for every Borel additive Haar measure and
  every scalar function, without any integrability hypothesis.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberIntegral_lowerMixedSubgroup_mul` (theorem): Left invariance under every element of the actual lower mixed subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalAverage` (def): The rectangular average on the actual quotient `Lminus \ G`: the actual descent of the
  left-`Lminus`-invariant fiber integral. No coset representative is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalAverage_mk` (theorem): Representative evaluation of the rectangular average.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint` (def): The first-block fiber map `([v], g) ↦ [I(v) g]_{H⁻}` from the small quotient
  `N_a \ GL_a` to `H⁻ \ G`, by actual quotient descent: left multiplication of `v` by
  `n ∈ N_a` multiplies `I(v) g` on the left by `I(n) ∈ H⁻`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint_mk` (theorem): Representative formula: `firstBlockFiberPoint [v] g = [I(v) g]_{H⁻}`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_firstBlockFiberPoint` (theorem): The first-block fiber map is jointly continuous in `(q, g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding` (theorem): The block identity `I(v) R(Z0) D(a0, n) = R(Z0 v⁻¹) diag(1, n) I(v a0)`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerRadical_mul_leviEmbedding_one_mem` (theorem): The first two factors `R(Z0 v⁻¹) diag(1, n)` of the block identity lie in `H⁻`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul` (theorem): Change of fiber: for `l = R(Z0) D(a0, n)`, left multiplication of the base point by `l`
  is right translation of the small quotient by `a0`.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberIntegral` (def): The inner slice integral of JPSS (4.9), (8): the total Bochner integral
  `∫_{N_a \ GL_a^k} f(firstBlockFiberPoint q g) dμA(q)` over the published small slice, for
  the supplied measure on the Borel structure of the small quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberIntegral_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul` (theorem): Left invariance under `l = R(Z0) D(a0, n)`, without any integrability hypothesis: right
  translation by `a0` preserves `μA` and, since `ord(det a0) = 0`, the small slice.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberIntegral_lowerMixedSubgroup_mul` (theorem): Left invariance under every element of the actual lower mixed subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockAverage` (def): The first-block slice average on the actual quotient `Lminus \ G`: the actual descent
  of the left-`Lminus`-invariant inner slice integral. No coset representative is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockAverage_mk` (theorem): Representative evaluation of the first-block slice average.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.ext_entryBlock`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerRadical_zero_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerRadical_zero_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerRadical_one_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerRadical_one_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_levi_zero_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_levi_zero_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_levi_one_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_levi_one_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerProduct_zero_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerProduct_zero_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerProduct_one_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.entryBlock_lowerProduct_one_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerRadical_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerRadical_add`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_inv`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.mem_oppositeParabolic_of_entryBlock`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.oppositeParabolic_factorization`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_lowerRadical`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_entryBlock`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerProduct_one`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinant_lowerRadical`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.continuous_lowerProduct`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv_symm_apply_radical`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv_symm_apply_snd`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupEquiv_inv`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.isUnit_entryBlock_zero_zero`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromMixed_surjective`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromLower_surjective`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromMixed_rightTranslate`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.projectionFromLower_rightTranslate`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.t2Space_lowerMixedQuotient`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.mem_determinantSlice`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.disjoint_determinantSlice`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.pairwise_disjoint_determinantSlice`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.iUnion_determinantSlice`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder_rightTranslate`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.rightTranslate_mem_determinantSlice`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerRadical_mul_leviEmbedding_blockPair`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.leviEmbedding_blockPair_mul_lowerRadical`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockEmbedding_mul_lowerRadical`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.leviEmbedding_blockPair_mem_lowerBlockUnipotent`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockEmbedding_mem_lowerBlockUnipotent`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberPoint_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalFiberIntegral_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.radicalAverage_rightTranslate`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantOrder_firstBlockFiberPoint`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint_mem_determinantSlice_iff`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockFiberIntegral_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockAverage_rightTranslate`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
