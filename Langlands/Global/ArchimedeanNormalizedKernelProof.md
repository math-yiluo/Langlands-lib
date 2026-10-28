# Normalized compact smooth kernels in identity neighborhoods: proof

Author: Worker 793.

The theorem `Langlands.Global.ArchimedeanGL.normalizedCompactKernel` in
`Langlands.Global.ArchimedeanNormalizedKernelProof` proves the exact published
`NormalizedCompactKernelStatement K n` for every `K : Type u` with
`[Field K] [NumberField K]` and every natural rank `n`, including zero. It has
no additional hypotheses. The final example checks its complete parameter
order and arbitrary universe.

This is an internal derived proof. It uses the standard bump-function
construction and claims to reproduce no literature proof. Write
`G = InfiniteAdelicGL K n` with its original completion-based topology. The
proof keeps the published smooth carrier `smoothFunctions K n` unchanged. That
carrier consists of functions whose composite with
`(archimedeanGLCoordinates K n).symm` is real `ContMDiff` of order `∞` on the
units manifold `ArchimedeanGL K n`. This module imports only the statement
module, Mathlib's finite-dimensional bump functions
(`Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension`) and Mathlib's set
integrals.

## Matrix coordinates

`matrixCoordinates K n : G → ArchimedeanMatrix K n` is the composite of the
published continuous multiplicative equivalence `archimedeanGLCoordinates K n`
with `Units.val`. Its codomain is the finite-dimensional real matrix space over
`mixedEmbedding.mixedSpace K`, with the operator norm from
`Matrix.Norms.Operator` used by the published smooth structure. Three helper
results follow:

- `matrixCoordinates_one` states that the identity maps to the identity matrix.
- `isOpenEmbedding_matrixCoordinates` composes the homeomorphism
  `(archimedeanGLCoordinates K n).toHomeomorph` with Mathlib's
  `Units.isOpenEmbedding_val`.
- `ofReal_comp_matrixCoordinates_mem` shows that if `b` is a real `C^∞`
  function on the matrix space, then `g ↦ (b (matrixCoordinates K n g) : ℂ)`
  belongs to `smoothFunctions K n`. On `ArchimedeanGL K n` the composite is
  `x ↦ (b x : ℂ)`, because `ContinuousMulEquiv.apply_symm_apply` cancels the
  coordinate equivalence. This composite is `ContMDiff`: it is the `C^∞` map
  `Complex.ofRealCLM ∘ b` composed with Mathlib's `Units.contMDiff_val`.

## Construction of the kernel

Fix a Borel measurable structure, a left Haar measure `μ` and `U ∈ 𝓝 1`.
Write `p = matrixCoordinates K n`.

1. Because `p` is an open embedding, `map p (𝓝 1) = 𝓝 (p 1) = 𝓝 1`, so
   `p '' U` is a neighborhood of the identity matrix. The proof chooses
   `r > 0` with `closedBall 1 r ⊆ p '' U`.
2. Let `φ` be Mathlib's `ContDiffBump` centered at the identity matrix with
   inner radius `r / 2` and outer radius `r`. The matrix space is
   finite-dimensional, so Mathlib provides `HasContDiffBump` for it. Then
   `φ` is real `C^∞` and nonnegative, its support is `ball 1 r`, and
   `φ 1 = 1`.
3. Let `S = p ⁻¹' closedBall 1 r`. By injectivity of `p`, `S ⊆ U`. The closed
   ball is compact because finite-dimensional real normed spaces are proper.
   It lies in the range of `p`, so `IsInducing.isCompact_preimage'` makes `S`
   compact. `S` is closed by continuity of `p`. Any function vanishing
   wherever `φ ∘ p` vanishes has support in `p ⁻¹' ball 1 r ⊆ S`. Hence its
   closed support also lies in `S`.
4. Let `b = φ ∘ p` and `b' g = b g⁻¹`. Then `b` is continuous with compact
   support. `HasCompactSupport.comp_homeomorph` with the inversion
   homeomorphism gives the same for `b'`, which is nonnegative with
   `b' 1 = φ 1 = 1`. A Haar measure is finite on compact sets and positive on
   nonempty open sets. Hence
   `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` gives
   `0 < I = ∫ g, b' g ∂μ`. Set `c = I⁻¹ > 0`.
5. The kernel's underlying function is `κ g = ((c * φ (p g) : ℝ) : ℂ)`. It is
   smooth by `ofReal_comp_matrixCoordinates_mem` applied to the `C^∞` function
   `c • φ`. Its closed support lies in `S` by step 3. `S` is compact and closed
   supports are closed, so `κ` has compact support and is an element of
   `SmoothCompactKernel K n`.

## Verification of the four conclusions

- `tsupport κ ⊆ S ⊆ U`.
- For every `g`, `(κ g).re = c * φ (p g) ≥ 0` and `(κ g).im = 0`, since `κ g`
  is the image of a nonnegative real number.
- `(κ 1).re = c * φ 1 = c > 0`.
- Since `κ (g⁻¹) = ((c * b' g : ℝ) : ℂ)`, `integral_complex_ofReal` and
  `integral_const_mul` give the following. Its integral is the image of
  `c * I = I⁻¹ * I = 1`.

  ```text
  ∫ g, κ (g⁻¹) ∂μ = ((c * ∫ g, b' g ∂μ : ℝ) : ℂ) = 1.
  ```

The normalization is of the inverse-kernel integral, as the statement
requires, and not of `∫ κ ∂μ`. Of the Haar hypothesis the proof uses only
finiteness on compact sets and positivity on open sets. It uses no left
invariance, inversion invariance or unimodularity, and no normalization of
`μ`. The Borel hypothesis supplies measurability of the continuous integrands.

## Rank zero and scope

The argument has no case split on `n`. At rank zero the matrix space is the
zero-dimensional real space and the group is a singleton. The bump function,
compactness and integral steps apply unchanged.

The module sets `backward.isDefEq.respectTransparency false`, as the published
smooth-differential modules do. Without it the units chart instance
`ChartedSpace (ArchimedeanMatrix K n) (ArchimedeanGL K n)` is not found. It also uses
`open scoped Classical` for the finiteness instances on the real and complex
place subtypes, as `ArchimedeanGL` does. The prospective route through
`SmoothBumpFunction.nhds_basis_tsupport` was not needed. The units manifold has
the single global chart `Units.val`, so a Euclidean `ContDiffBump` in that chart
is already a smooth bump on the actual group.

This module proves kernel existence only. It asserts nothing about convolution
convergence, derivative-topology approximation, compact conjugation averaging,
reproducing kernels, or automorphic differential growth.
