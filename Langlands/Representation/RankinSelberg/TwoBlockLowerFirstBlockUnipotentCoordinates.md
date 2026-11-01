# Block coordinates of the prescribed lower-unipotent Haar

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates`.
Authors: Worker 1179.

This helper module writes the prescribed Haar measure on the lower block
unipotent group `H⁻` in block coordinates. It is support for the first-block
slice tower of JPSS (1983), Section 4.9, equation (8), printed page 418, proved
in the companion module `TwoBlockLowerFirstBlockSliceTower`. It contains only
theorems; it introduces no definition and no statement.

## Setting

For a two-block shape `h : ∑ i, (m i + 1) = t + 1` put `a = m 0 + 1` and
`b = m 1 + 1`. The published lower-unipotent data supply:

- `blockRotation h R = C`, the inverse of the block-reversing permutation
  matrix of the shape;
- `lowerRadical h R Z = C⁻¹ u'(Z) C`, the lower radical matrix
  `[[1, 0], [Z, 1]]` for `Z` a `b × a` matrix, where `u'` is the upper
  radical of the reversed shape `(b, a)`;
- `lowerBlockUnipotent h F.Carrier = H⁻ = C⁻¹ N C`, with its prescribed Haar
  measure `lowerHaar F h`, defined as the transport of the standard full
  unipotent Haar `unipotentHaar F.Carrier t` by `n ↦ C⁻¹ n C`.

Write `diag(x, y)` for
`(succBlockShape m h).leviEmbedding R (blockPair R (x, y))`, and, for an
additive Haar `μR` on `b × a` matrices, write `c(μR) = μR {Z | ∀ i j, Z i j ∈ O}`
for its integral-cube mass (`O` the valuation integers of the field).

## Results

Algebraic part, over any commutative ring `R`:

- `reverseMatrix_mul_reverse_leviEmbedding`: for any block shape, conjugating
  a Levi element of the reversed shape by the block-reversing matrix gives the
  Levi element with reversed block labels.
- `blockRotation_inv_mul_blockEmbedding_mul`: `C⁻¹ diag'(n₀, n₁) C =
  diag(n₁, n₀)`, where `diag'` is the block-diagonal embedding of the reversed
  shape.
- `blockRotation_inv_mul_coordinates_mul`: `C⁻¹ (diag'(n₀, n₁) u'(Z)) C =
  diag(n₁, n₀) R(Z)`, with `R(Z) = lowerRadical h R Z`.

Measure part, over a canonical p-adic field `F` with its canonical topology and
Borel structures:

- `lintegral_lowerHaar_eq`: the `lowerHaar` integral of `ψ ∘ val` is the
  `unipotentHaar` integral of `n ↦ ψ(C⁻¹ n C)`, for measurable
  `ψ : GL_{t+1} → ℝ≥0∞`. This unfolds the definition of `lowerHaar`.
- `lintegral_unipotentHaar_blockCoordinates`: for any two-block shape `h'`
  with blocks `m'`, any additive Haar `μR` on the upper rectangular matrices and
  measurable `φ ≥ 0` on `N = upperUnipotent (t + 1)`,
  `c(μR) ∫_N φ = ∫_{N_{m'0+1}} ∫_{N_{m'1+1}} ∫ φ(n(y, x) u(Z)) dμR`, where
  `n(y, x) u(Z)` is the published block coordinate map
  `TwoBlockUnipotentQuotientIntegration.coordinates`.
- `lintegral_lowerHaar` (the main result): for any additive Haar `μR` on
  `b × a` matrices and measurable `ψ : GL_{t+1} → ℝ≥0∞`,

  `c(μR) · ∫_{H⁻} ψ(x) d(lowerHaar F h)(x) =
    ∫_{y ∈ N_b} ∫_{x ∈ N_a} ∫_Z ψ(diag(x, y) R(Z)) dμR(Z) dx dy`,

  with `N_a`, `N_b` carrying `unipotentHaar F.Carrier (m 0)` and
  `unipotentHaar F.Carrier (m 1)`.

## Proof

The algebraic identities are entrywise computations: block indices are
decomposed with `indexEquiv` and `Fin.rev`, and the published entry formula
for conjugation by the reversing matrix is applied. The coordinate identity
then follows from `lowerRadical = C⁻¹ u'(Z) C` by group rewriting.

For `lintegral_unipotentHaar_blockCoordinates`, the published identity
`map_coordinates_prod` states that the coordinate map pushes the product of the
block-unipotent measure and `μR` forward to `c(μR) · unipotentHaar`. The proof
rewrites the scalar as a smul of the measure, applies `lintegral_map`, splits
the product integral by Tonelli (`lintegral_prod`), and unfolds the
block-unipotent measure into the two diagonal unipotent Haar measures with
`lintegral_blockHaar`.

For `lintegral_lowerHaar`, the proof first applies `lintegral_lowerHaar_eq`,
then the previous block-coordinate formula for the reversed shape
`(m 1, m 0)` (via `reverse_sum h`), and finally rewrites each integrand point
`C⁻¹ (diag'(y, x) u'(Z)) C` as `diag(x, y) R(Z)` by
`blockRotation_inv_mul_coordinates_mul`. The rectangular measure `μR` is
arbitrary throughout; the cube mass `c(μR)` is the only normalization factor.

## Provenance

This is derived internal support. JPSS (1983), Section 4.9, equation (8),
printed page 418, integrates over `H_{t₁,t₂} \ G_r`; the lower block unipotent
group is specified on printed page 413. The source does not state block
coordinates for its Haar measure; the coordinate formula above is the routine
Fubini decomposition used to evaluate the left side of equation (8) in the
companion module, and it is not claimed to appear in the source.
