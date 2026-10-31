# Haar measure of `GL_(t+1)` in two-block parabolic coordinates

Module `Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar`.
Author: Worker 1112.

## Setting

`t : ℕ`, `m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`; the block shape is
`succBlockShape m h` with blocks of sizes `n₀ = m 0 + 1` and `n₁ = m 1 + 1`, its
upper parabolic `P`, Levi `GL_{n₀} × GL_{n₁}` (as `(succBlockShape m h).Levi`) and
the upper radical `TwoBlockJacquet.upperRadical h R x = [[1, x], [0, 1]]`.

## Algebra (any commutative ring `R`)

- `blockEquiv h : Fin n₀ ⊕ Fin n₁ ≃ Fin (t + 1)` is
  `finSumFinEquiv.trans (finCongr (blockRanks_add h))`, the convention of
  `TwoBlockJacquet.upperRadical`; `blockEquiv_inl/inr` identify it with the block
  indices `(succBlockShape m h).index 0/1`.
- `val_eq_reindex_fromBlocks`: a matrix of `GL_(t+1)` with prescribed block entries
  is `Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B C D)`.
  Consequently `leviEmbedding_val` (block diagonal `fromBlocks a 0 0 d`) and
  `upperRadical_val` (`fromBlocks 1 x 0 1`); `reindex_mul_reindex` multiplies
  reindexed block matrices.
- `parabolicPoint h (L, x) = leviEmbedding L * upperRadical h R x` (definition), with
  matrix `reindex (fromBlocks a (a * x) 0 d)` (`parabolicPoint_val`, by
  `Matrix.fromBlocks_multiply`) and determinant `det a * det d`
  (`det_parabolicPoint`, `Matrix.det_fromBlocks_zero₂₁`).
- `upperRadical_mul_leviEmbedding`: `u(y) m = m u(a⁻¹ y d)`, again by block
  multiplication. Hence `parabolicPoint_inv_mul`:
  `parabolicPoint (L₀, x₀)⁻¹ * parabolicPoint (L, x) =
   parabolicPoint (L₀⁻¹ L, x - a'⁻¹ x₀ d')` with `(a', d') = L₀⁻¹ L`; the map
  `parabolicShift h (L₀, x₀)` is this right-hand parameter, and
  `parabolicPoint_parabolicShift` restates the identity.
- `corner` is the upper-right block; `parabolicCoord q = (leviProjection q, a⁻¹ ·
  corner q)` for `q ∈ P`. `parabolicPoint_mem` (block `(1,0)` vanishes, via
  `mem_parabolic_iff`), `parabolicPoint_parabolicCoord`,
  `parabolicCoord_parabolicPoint` and `exists_parabolicPoint_eq` show that
  `parabolicPoint` is a bijection onto `P` with inverse `parabolicCoord`.
- `exists_parabolicPoint_mul`: a factorization `G = P K` (in the form supplied by
  `exists_compactProductCoefficientFormula`) gives `y = parabolicPoint z * k` with
  `k ∈ K`.

## Topology

`continuous_parabolicPoint`, `continuous_corner`, `continuous_parabolicCoord` over a
topological ring, from the continuity of the Levi embedding and projection, of
`upperRadical`, of inversion in `GL`, and of matrix multiplication.

## Measures (canonical p-adic field)

With the canonical topology, Borel structures on the field and on each `GL_(n+1)`,
and a supplied additive Haar measure `dx` on `n₀ × n₁` matrices:

- `parabolicMeasure F h dx = (Measure.pi fun i => generalLinearHaar F.Carrier (m i)).prod dx`
  (definition): the normalized block Haar measures times `dx`, with no density. It
  is σ-finite, positive on open sets and finite on compact sets (instances).
- `measurePreserving_parabolicShift`: `parabolicShift (L₀, x₀)` preserves it. Proof:
  it is the skew product of left multiplication by `L₀⁻¹` on the Levi (left
  invariance of the product Haar measure) with the translations
  `x ↦ x - a'⁻¹ x₀ d'` of `dx` (`MeasurePreserving.skew_product`).
  `parabolicPoint_translation` packages this as the hypothesis `hσ` of the
  factorization integral.
- `parabolicMeasure_preimage_ne_zero` (for an open subgroup `K`: its preimage is a
  nonempty open set containing `(1, 0)`) and `parabolicMeasure_preimage_ne_top` (for a
  compact subgroup `K`: the preimage lies in the image under the continuous
  `parabolicCoord` of the compact set `P ∩ K`, compact because `P` is closed).
- Radical scaling: `map_mul_left_radical` (`dx.map (a * ·) = |det a|^(-n₁) • dx`,
  from `padicRectangularHaarScaling`), `integral_mul_left_radical`
  (`∫ Ψ (a x) dx = |det a|^(-n₁) • ∫ Ψ dx` for every `Ψ`, since `x ↦ a x` is a
  measurable embedding, `measurableEmbedding_mul_left_radical`) and
  `integrable_mul_left_radical_iff`. Here `|det a|` is
  `F.canonicalTopologicalData.determinantNorm`.
- For a compact open subgroup `K` with `GL_(t+1) = P K`:
  `integrable_parabolic_iff` (integrability of `f` for `generalLinearHaar F.Carrier t`
  is equivalent to integrability of `(k, z) ↦ f (parabolicPoint z * k)` for
  `μ|_K × parabolicMeasure`) and `integral_parabolic`
  (`∫ k in K, ∫ z, f (parabolicPoint z * k) d(parabolicMeasure) dμ =
   (parabolicMeasure (parabolicPoint ⁻¹' K)).toReal • ∫ f dμ`). Both apply the
  generic `Langlands.CompactFactorization.integrable_comp_mul_iff` and
  `integral_restrict_integral_mul` to the hypotheses above.

## Provenance and scope

This is the two-block case of the integration formula `dg = dp dk` over
`G = P K` used by Godement–Jacquet, *Zeta Functions of Simple Algebras* (1972),
Theorem 3.4, printed page 38 onward. The normalization constant is not computed:
the formulas carry the explicit positive finite constant
`parabolicMeasure (parabolicPoint ⁻¹' K)`. In the coordinates `(L, x)` with
`parabolicPoint (L, x) = [[a, a x], [0, d]]` the left Haar measure of `P` has no
density; the factor `|det a|^(-n₁)` of the coordinates `[[a, b], [0, d]]` appears
only through the separate radical scaling lemma. The measure `dx` is any additive
Haar measure (for example the product of a supplied self-dual scalar measure).
