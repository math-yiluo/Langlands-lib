# Radical coordinates on the upper unipotent group and Haar transport

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientCoordinates`,
namespace `Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration`.

Author: Worker 235.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`
(JPSS 1983, Section 4.6, printed pages 411-412). It shows that the upper
unipotent group `N` of `GL_(t+1)` is the product `H × R` of the block-diagonal
unipotent subgroup `H` and the rectangular matrices `R`, by the coordinates
`(b, x) ↦ b u(x)`. As a homeomorphism, these coordinates carry a left-invariant
measure on `H` of mass one on its integral points, times any additive Haar measure
`μR` on `R`, to `c • unipotentHaar`, where `c` is the `μR`-mass of the integral
rectangle. The module constructs no quotient measure and no kernel, and proves no
statement about quotients.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`), Section 4.6, printed pages
411-412, integrate over `N \ GL_(t+1)` by first integrating over the fibres of
`H \ GL_(t+1) → N \ GL_(t+1)`. The fibres are parametrized by the upper-right
block `x ∈ M(t₁ × t₂)`. The source uses the decomposition `N = H ⋉ R` and the
matching factorization of Haar measures without stating them. Their proofs here
are internal content of this proof.

The setting is the published
`Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData` and
`TwoBlockDeformationCell`. There `h : ∑ i, (m i + 1) = t + 1`, the blocks have
ranks `m 0 + 1` and `m 1 + 1`, and `upperRadical h K x = (1 x; 0 1)`.
`blockUnipotent h K` is the subgroup `H` of block-diagonal matrices
`diag(n₀, n₁)` with `nᵢ` upper unipotent, and `blockUnipotentEquiv` and
`blockUnipotentHomeomorph` identify `H` with the product of the two block
unipotent groups. `unipotentLevi h n i` is the `i`-th diagonal block of an upper
unipotent `n`, `unipotentCorner h n = β` is its upper-right block, and
`unipotentShift h n x = n₀⁻¹ (β + x n₁)`. The published factorization is
`upperRadical_mul_upperUnipotent`: `u(x) n = diag(n₀, n₁) u(n₀⁻¹ (β + x n₁))`.

## Algebra (section `Algebra`, any field `K`)

- `radicalCoord h n := unipotentShift h n 0 = n₀⁻¹ β`, the radical coordinate of
  an upper unipotent `n`.
- `blockPart h n ∈ H`, the block-diagonal part `diag(n₀, n₁)`, and
  `blockPart_val`, which gives its matrix.
- `blockPart_mul_upperRadical`: `n = diag(n₀, n₁) u(n₀⁻¹ β)`. This is the
  published factorization at `x = 0`.
- `upperRadical_mem_blockUnipotent_iff`: `u(x) ∈ H ↔ x = 0`.
- `coordinates h (b, x) := b u(x)`, an element of `N`, with `coordinates_val` (simp)
  and `coordinates_injective`. The proof of injectivity uses
  `u(x) u(y)⁻¹ = u(x - y)` and the previous item.
- `coordinates_blockPart_radicalCoord` and the equivalence
  `coordinatesEquiv : H × R ≃ N` with inverse `n ↦ (blockPart h n, radicalCoord h n)`.
  `radicalCoord_coordinates` (simp) recovers the radical coordinate.
- `leviEmbedding_unipotentLevi`: an element of `H` is the Levi embedding of its
  own diagonal blocks.
- `mul_coordinates`: left multiplication in coordinates. For `n ∈ N`,
  `n · b u(x) = (diag(n₀, n₁) b) u(s + x)` with
  `s = unipotentShift h b (radicalCoord h n)`. The proof combines
  `blockPart_mul_upperRadical` for `n` with the published factorization for
  `u(n₀⁻¹ β) b`.

## Topology (section `Topology`, `K` a topological field)

- `continuous_unipotentCorner`, `continuous_unipotentLevi_inv_zero`,
  `continuous_unipotentLevi_one`: continuity of the corner block, of `n₀⁻¹` and of
  `n₁` as matrices.
- `continuous_unipotentShift`: joint continuity of `(n, x) ↦ n₀⁻¹ (β + x n₁)`.
  `continuous_unipotentShift_left` gives continuity in `n` along any continuous
  family, for a fixed `x`.
- `continuous_radicalCoord`, `continuous_blockPart`, `continuous_coordinates`.
- `coordinatesHomeomorph : H × R ≃ₜ N`, the coordinates as a homeomorphism, with
  `coordinatesHomeomorph_apply` (simp).

## Integral points (section `Integral`)

Here `O` is the valuation ring of `K` and `Conductor.integralSubgroup O t` is the
group of matrices `g` with `g` and `g⁻¹` integral.

- `forall_index`: a property of all pairs of indices of `Fin (t + 1)` is checked on
  the four blocks.
- `mem_blockUnipotent_index_zero_one`, `mem_blockUnipotent_index_one_zero`: the
  off-diagonal blocks of an element of `H` vanish.
- `mul_upperRadical_index_same`, `upperRadical_mul_index_same`: multiplying an
  element `g ∈ H` by a radical element on either side does not change the
  diagonal blocks of `g`.
- `upperRadical_mem_integralSubgroup_iff`: `u(x)` is integral exactly when every
  entry of `x` lies in `O`. Here `u(x)⁻¹ = u(-x)`.
- `mem_integralSubgroup_of_mul_upperRadical`: if `g u(x)` is integral for
  `g ∈ H`, then so is `g`. The diagonal blocks of `g` and `g⁻¹` are those of
  `g u(x)` and `u(-x) g⁻¹ = (g u(x))⁻¹`, and the other blocks vanish.
- `coordinates_mem_integralSubgroup_iff`: `b u(x)` is integral exactly when `b` is
  integral and all entries of `x` lie in `O`.
- `blockEmbedding_mem_integralSubgroup_iff`: `diag(n₀, n₁)` is integral exactly
  when each block `nᵢ` is.

## Haar transport (section `Transport`)

Here `F` is a nonarchimedean local field that is Hausdorff and second countable,
with Borel σ-algebras on `F`, `H` and `N`. `R` carries Mathlib's product
σ-algebra on matrices, which is Borel.

- `isMulLeftInvariant_map_coordinates`: for a left-invariant s-finite measure `μH`
  on `H` and an additively left-invariant s-finite measure `μR` on `R`,
  `map (coordinates h) (μH.prod μR)` is left invariant on `N`. By
  `mul_coordinates`, left translation by `n` becomes the skew product
  `(b, x) ↦ (diag(n₀, n₁) b, s_b + x)`. This is a left translation of `H`
  followed by fibrewise translations of `R`, so it preserves `μH.prod μR`
  (Mathlib `MeasurePreserving.skew_product`).
- `coordinates_preimage_unipotentIntegralOpen`: the preimage of the integral
  points `unipotentIntegralOpen F t` of `N` is the product of the integral points
  of `H` and the integral rectangle `{x | ∀ a c, x a c ∈ O}`.
- `map_coordinates_prod` (main result): suppose `N` is second countable, `μH` is
  left invariant, s-finite and finite on compacts with
  `μH {b | b ∈ integralSubgroup} = 1`, and `μR` is an additive Haar measure.
  Then

  `map (coordinates h) (μH.prod μR) = μR {x | ∀ a c, x a c ∈ O} • unipotentHaar F t`.

  The left side is left invariant (above) and finite on compacts, because it is
  the pushforward along a homeomorphism. Mathlib's uniqueness of Haar measure
  (`Measure.isMulLeftInvariant_eq_smul`) makes it a scalar multiple of
  `unipotentHaar F t`. Evaluating on the integral points finds the scalar. The
  left side gives `1 · c` by the previous item and `Measure.prod_prod`, and
  `unipotentHaar F t` has mass one there (`unipotentHaar_integral`).
- `blockMeasure_integral`: the transported block measure
  `map (blockUnipotentEquiv h F) (pi fun i => unipotentHaar F (m i))`, the measure
  `μH` of the target statement, has mass one on the integral points of `H`. Under
  `blockUnipotentEquiv`, the integral points are the product of the integral
  points of the two blocks (`blockEmbedding_mem_integralSubgroup_iff`), and each
  block's normalized Haar measure has mass one there.
