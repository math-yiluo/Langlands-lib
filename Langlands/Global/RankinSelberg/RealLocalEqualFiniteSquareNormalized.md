# Entire products for an orthogonal-finite square test in the real equal-rank unfolding

This module is the real counterpart of the complex module
`ComplexLocalEqualFiniteSquareNormalized`, together with the matched compact expansion of
`ComplexLocalMatchedMatrixExpansion`. Let `m = t + 1` and `n = t + 2`, and let `O` be the real
orthogonal group `Matrix.unitaryGroup (Fin n) ℝ` with its Haar measure.

## Definitions and small lemmas

* `charData_inverse`: the inverse of the real character `charData e z` (parity `e`,
  exponent `z`) is `charData e (-z)`.
* `realStandardMatrixCoefficient es ℓ f g = ℓ(π(g) f)`. Here `f` is a standard `K`-finite
  vector of the block list `es`, included into the smooth position principal series of
  `expand es` by `RealPrincipalSeries.expandedSmoothInclusion`. `π(g)` is the right translation
  `RealPrincipalSeries.translate`, and `ℓ` is a linear form. These are the matrix coefficients
  produced by `RealStandardCompactBanach.exists_compactProjection_coefficients`.
* `realWeightedMatrixIntegral μ e Ψ b w = ∫ Ψ(g) sgn(det g)^e |det g|^(w + m/2) b(g) dμ(g)`, the
  matrix integral of `RealLocalEqualShiftedProducts`, with the weighted test
  `realWeightedMatrixTest (charData e 0) Ψ (w + m/2)`.
* Private strip-growth lemmas (constant, sum, shift and tilt), copied from the complex module.

## The statement

`RealLocalEqualFiniteSquareNormalizedStatement t` fixes real quotient data `D` (rank `t`) and
`D'` (rank `t + 1`), a nonzero real `a`, a parity `e`, and real character lists `cs` and `fs`
of lengths `m` and `n`, with block lists `ds = cs.map character` and `es = fs.map character`.
It assumes the following.

1. `W` lies in the uniform Whittaker model of rank `m` for `ds` and `a`.
2. `B` is a uniform Whittaker map on the standard `K`-finite module of `es` with character
   `-a`. It has a continuous Whittaker evaluation `L` (`IsWhittakerStandardEvaluation`). This
   is an explicit hypothesis. The Library's `realSmoothWhittakerEvaluation` supplies such an
   evaluation only under two premises: the Casselman–Wallach extension premise and
   irreducibility of the standard module (`IsIrreducibleGKModule`). At arbitrary inducing
   exponents the standard module can be reducible. `f` is a standard vector.
3. `Ψ` is a square Schwartz test whose left translates `X ↦ Ψ(k⁻¹ X)`, for `k` in the orthogonal
   subgroup `unitaryCompact ℝ n`, span a finite-dimensional space. This is the condition of
   `RealOrthogonalSchwartzDensityStatement`.
4. (Corank-one input.) For every `V` in the uniform model of rank `n` for `es` and `-a`, the
   corank-one integral `realUnequalIntegral` of `(V, W)` and its dual
   `realUnequalDualIntegral` (parameter `-a`) satisfy `HasRealPairNormalizedGrowth` with lists
   `xs, ys, xsd, ysd`, epsilon data `bA, cA` and sign `signA`. All of these are arbitrary in the
   statement.
5. (Matrix input.) Let `ℓ` be any linear form with a compact derivative bound
   (`HasCompactDerivativeBound`), and let `b_ℓ` be its matrix coefficient. Then on some right
   half-plane in `w` the integrands of `realWeightedMatrixIntegral` are integrable for
   `D'.groupHaar`. This holds for the test `Ψ` with `b_ℓ`, and for the Fourier test
   `Ψ̂ = realRectangularSchwartzFourier (-a) Ψ` with `b_ℓ ∘ (inverse transpose)`. Moreover the
   two matrix integrals satisfy `HasRealPairNormalizedGrowth` with arbitrary lists
   `us, vs, usd, vsd`, epsilon data `bM, cM` and sign `signM`.

The conclusion provides two functions `F` and `Fd` on `ℂ × ℂ`, both complex differentiable on
all of `ℂ²`. Each has exponential growth on vertical strips in `s`, both along the lines with
fixed `z` and along the tilted lines `z = v + s`. They satisfy:

* For `Re z > τ` and `Re s > σ`:
  `F(z, s) = den(xs, ys)(s) · den(us, vs)(s + z) · ∫ equalUnfoldedKernel (charData e z) Ψ W (B f) s`.
  The integral is over `D.measure × D'.groupHaar`, and `den` is the reciprocal real pair
  `L`-factor.
* For `Re(-z) > τ_d` and `Re s > σ_d`:
  `Fd(z, s) = den(xsd, ysd)(s) · den(usd, vsd)(s - z) · ∫ equalUnfoldedKernel (charData e (-z)) Ψ̂ W̃ (B f)~ s`.
  Here `W̃` and `(B f)~` are the Weyl inverse-transpose duals (`ArchimedeanLocal.dualFunction`).
* For all `z, s`:
  `Fd(z, 1 - s) = signA · ε(xs, ys; bA, cA)(s) · signM · ε(us, vs; bM, cM)(s + z) · F(z, s)`.

The thresholds `τ, σ, τ_d, σ_d` may depend on `Ψ` and `f`.

## Proof

1. `realOrthogonalMatchedWeight` (from `RealLocalCompactFourierWeight`) gives one continuous
   weight `κ ∈ finiteWeights` on `O`. With the parity character `charData e 0`, it reproduces both
   `Ψ` and `Ψ̂`.
2. `exists_compactProjection_coefficients` (from `RealWhittakerCompactProjection`) for `B`, `L` and `κ` gives vectors `u_j`
   and bounded linear forms `ℓ_j` with
   `∫ κ(k) (B f)(x k g) dk = ∑_j (B u_j)(x) b_j(g)`, where `b_j = realStandardMatrixCoefficient es ℓ_j f`.
   `dualFunction_compactExpansion` turns this into the dual expansion with the duals of
   `B u_j` and `b_j ∘ (inverse transpose)`.
3. The Library's finite-product theorem `realLocalEqualShiftedProducts` (from
   `RealLocalEqualShiftedProducts`) is applied twice, with `K = O` and `ι = Unitary.toUnits`
   (orthogonal matrices have `|det| = 1` by `MaximalParabolicIntegration.abs_det_unitary`).
   * The primal application uses `ds, es, a, W, B f, Ψ` and the matrix integrals
     `Z_j = realWeightedMatrixIntegral D'.groupHaar e Ψ b_j`.
   * The dual application uses the dual character lists `dualCharacterBlocks cs, fs`, the
     parameter `-a`, the duals of `W` and `B f`, the test `Ψ̂` and the dual matrix integrals.
   * The dual memberships come from the Library's `realUniformWhittakerCharacterDual`. The
     half-plane integrability of the matrix integrals comes from the matrix input, with one
     common threshold for the finitely many `j`.
   * This gives, on chambers, `∫ kernel = ∑_j Ψ(s; B u_j, W) Z_j(s + z)` and the dual analogue
     with `Zd_j(s - z)`.
4. Input (4) for `V = B u_j` gives entire `N_j, Nd_j`, and input (5) for `ℓ_j` gives entire
   `M_j, Md_j`. Put `F(z, s) = ∑_j N_j(s) M_j(s + z)` and `Fd(z, s) = ∑_j Nd_j(s) Md_j(s - z)`.
   * On the chambers, enlarged so that `Re s` and `Re(s ± z)` exceed all normalization
     thresholds, the half-plane equalities of the normalized pairs give the two traces. On the
     dual side, the Library's `realUnequalDualIntegral_adjacent` (from
     `RealLocalAdjacentIntegrals`) rewrites the dual corank-one integral as the ordinary
     corank-one integral of the duals.
   * The pointwise equations `Nd_j(1 - s) = signA ε_A(s) N_j(s)` and
     `Md_j(1 - (s + z)) = signM ε_M(s + z) M_j(s + z)` give the reflection identity, because
     `(1 - s) - z = 1 - (s + z)`.
   * Strip growth follows from the closure lemmas. Along `z = v + s`, `F` involves `M_j(2s + v)`
     (a dilation, `HasStripExponentialGrowth.div_add`), and `Fd` has the constant second
     factor `Md_j(-v)`.

## Provenance and scope

This is Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2, pp. 56–58, for a left
`K_n`-finite square test. There the unfolded integral (8.1) becomes a finite sum of products of
corank-one integrals and matrix integrals on both sides of the functional equation. The
product of the two functional equations then continues the sum. The Lean statement follows
the complex module and keeps three explicit inputs:

* the continuous Whittaker evaluation of `B`, an explicit hypothesis (the Library's
  `realSmoothWhittakerEvaluation` provides it only for irreducible standard modules, under the
  Casselman–Wallach extension premise);
* the normalized corank-one equation for every coefficient of the larger model, which is the
  induction hypothesis;
* the normalized matrix equation for bounded matrix coefficients of the larger principal
  series. The Library does not prove it.

The module proves no statement about non-finite square tests, uniform chambers, the actual
equal-rank integrals, or `RealLocalUniformPositiveEqualContinuationStatement`.
`HasRealPairNormalizedGrowth` is the predicate of the module
`RealLocalNormalizedGrowth`.
