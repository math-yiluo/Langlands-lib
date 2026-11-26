# Compact averaging in the real unfolded adjacent-rank integral

Write `H = GL_(r+1)(ℝ)`, `N` for its upper unipotent subgroup, `Q = N \ H`, and let `D` be
real quotient measure data of rank `r`, with quotient measure `D.measure` on `Q` and Haar measure
`D.groupHaar` on `H`. Let `K` be a compact group with a finite measure `ν` and a continuous
homomorphism `ι : K → H`. Let `F` be a square Schwartz test on `(r+1) × (r+1)` real matrices
whose left translates `X ↦ F(ι(k)⁻¹ X)`, `k ∈ K`, span a finite-dimensional space. The module
moves a compact average from the square test of the unfolded adjacent-rank kernel
`realAdjacentUnfoldedKernel` of `RealLocalAdjacentUnfolding` to the second Whittaker function.
It is the real counterpart of the Library's `ComplexAdjacentCompactAverage`.

## Results

- `integrable_realAdjacentCompactFamily`. Fix a continuous weight `w` on `K`, a real character
  datum `c` with determinant character `η`, a continuous row function `f` of rapid decay, and
  continuous `U`, `V` on `H`. Assume `U(u g) V(u g z) = U(g) V(g z)` for `u ∈ N`, that `U`
  satisfies the gauge estimate `HasGauge`, and that `V` is bounded by a constant times a power
  of `realMatrixHeight`. Then on some right half-plane the function
  `(k, q, z) ↦ w(k) · realAdjacentUnfoldedKernel η (X ↦ F(ι(k)⁻¹ X)) f U V s (q, z)` is
  integrable for `ν × D.measure × D.groupHaar`.

- `realAdjacentCompactAverage`, the proof of `RealAdjacentCompactAverageStatement`. Assume in
  addition that `|det ι(k)| = 1` for every `k`, and that a continuous weight `κ` reproduces `F`
  in the form
  `∫_K κ(k) c(det ι(k)⁻¹) F(ι(k)⁻¹ A) dν(k) = F(A)` for every matrix `A`
  (the left side is written with `RealGodement.realCompactMatrixTranslate`). Then on some right
  half-plane the function
  `I(q, z) = realEqualIntegrand U (x ↦ ∫_K κ(k) V(x ι(k) z) dν(k)) f s q · realAdjacentMatrixWeight η F s z`
  is integrable on `Q × H`, and the integral over `Q × H` of the unfolded kernel of `(F, f, U, V)`
  equals the integral of `I`.

- `realAdjacentProductExpansion`, the proof of `RealAdjacentProductExpansionStatement`. If a
  function `V(x, z)` on `H × H` is a finite sum `Σ_j W_j(x) C_j(z)`, every
  `z ↦ realAdjacentMatrixWeight η F s z · C_j(z)` is `D.groupHaar`-integrable and every
  `realEqualIntegrand U (W j) f s` is `D.measure`-integrable, then the integral over `Q × H` of
  `realEqualIntegrand U (V(·, z)) f s q · realAdjacentMatrixWeight η F s z` is
  `Σ_j realEqualIntegral D U (W j) f s · ∫_H realAdjacentMatrixWeight η F s z · C_j(z) dz`.

## Proofs

For the integrability lemma, choose a basis of the span of the translates. Each basis vector is
the function of a Schwartz test, because a left translate of a Schwartz test by an invertible
matrix is again a Schwartz test. The evaluation functionals at matrices span the dual of the
finite-dimensional span, so every coordinate of `k ↦ (X ↦ F(ι(k)⁻¹ X))` is continuous in `k`.
The Library's `realAdjacentConvergence` gives a half-plane of integrability for each basis test,
and the finite sum of products of a continuous function on the compact group with these
integrable kernels is integrable on the maximum of the finitely many half-planes.

For the averaging statement, apply this lemma to the weight `k ↦ κ(k) c(det ι(k)⁻¹)`. The map
`(k, q, z) ↦ (k, q, ι(k) z)` preserves `ν × D.measure × D.groupHaar` by left invariance of the Haar
measure. Since `|det ι(k)| = 1`, the determinant power of `ι(k) z` equals that of `z`, and the
factor `c(det ι(k)⁻¹)` cancels against `η(det ι(k))`. After this change of variables the
integrand becomes `κ(k) · realEqualIntegrand U (x ↦ V(x ι(k) z)) f s q · realAdjacentMatrixWeight η F s z`.
Integrating first over `K` gives `I` on one side (the factors not involving `k` come out of the
compact integral) and, by the reproducing identity, the unfolded kernel of `(F, f, U, V)` on the
other. Fubini's theorem for the integrable joint function gives both conclusions.

The product expansion is pointwise distribution of the finite sum, integration of a finite sum,
and `integral_prod_mul` for each product of a function on `Q` and a function on `H`.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 59–60: Jacquet substitutes the identity
`∫ Φ₁(k⁻¹X) μ_n(det k)⁻¹ ξ(k) dk = Φ₁(X)` for an elementary idempotent `ξ` of `K_(n-1)` into the
integral (8.3) and changes `h` into `kh`. Here any continuous weight on any compact group
mapping into the matrices of absolute determinant one may be used, and the convergence needed for
the interchange of integrals is proved from the Library's `realAdjacentConvergence`.
