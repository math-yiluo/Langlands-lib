# The real equal-rank normalized unfolded integral for every square Schwartz test

This module is the real counterpart of the published complex module
`ComplexLocalEqualSquareLimit`. It passes from the orthogonal-finite square tests of
`RealLocalEqualFiniteSquareChambers` to arbitrary square Schwartz tests by a limit of entire
functions. Notation: `m = t + 1`, `n = t + 2`, `D` and `D'` real quotient data of ranks `t`
and `t + 1`, `den(xs, ys)` the reciprocal real pair `L`-factor, and `ε(xs, ys)` the real pair
`ε`-factor (`realPairEpsilon`) with the indicated additive parameter and scale.

## Statement

`RealLocalEqualSquareLimitStatement t` keeps the inputs of
`RealLocalEqualFiniteSquareChambersStatement` and adds three:

* the corank-one sign `signA` is nonzero;
* the matrix sign `signM` is nonzero;
* the matrix input `RealMatrixCoefficientNormalizedGrowth` holds for every square Schwartz test
  with finite-dimensional left orthogonal span.

The remaining inputs are:

* character lists `cs, fs` of lengths `m, n`;
* `W` in the uniform real Whittaker model of `cs` with character `a`;
* a uniform Whittaker map `B` for `fs` and `-a` with a continuous Whittaker evaluation, and a
  standard vector `f`;
* the normalized corank-one equation for all coefficients of the larger model paired with `W`
  (lists `xs, ys, xsd, ysd`, data `bA, cA`, sign `signA`);
* matrix data `us, vs, usd, vsd, bM, cM, signM`.

The conclusion gives thresholds `τ, σ, τ_d, σ_d`, independent of the test. For every square
Schwartz test `Ψ` there is a function `A` on `ℂ²` with the following properties:

* `A ∘ γ` is holomorphic for every holomorphic curve `γ : ℂ → ℂ²`;
* `s ↦ A(z, s)` has exponential growth on vertical strips for every `z`;
* for `τ < Re z` and `σ < Re s`,
  `A(z, s) = den(xs, ys)(s) · den(us, vs)(s + z) · ∫ equalUnfoldedKernel (charData e z) Ψ W (B f) s`,
  with the integral over `D.measure × D'.groupHaar`;
* for `τ_d < Re(-z)` and `σ_d < Re s`,
  `signA · ε(xs, ys)(1 - s) · signM · ε(us, vs)(1 - s + z) · A(z, 1 - s)`
  equals
  `den(xsd, ysd)(s) · den(usd, vsd)(s - z) · ∫ equalUnfoldedKernel (charData e (-z)) Ψ̂ W̃ (B f)~ s`.
  Here `Ψ̂ = realRectangularSchwartzFourier (-a) Ψ` and `~` is the Weyl inverse-transpose dual
  (`ArchimedeanLocal.dualFunction`).

## Proof

1. `realLocalEqualFiniteSquareChambers` gives the common chambers `τ, σ, τ_d, σ_d`. For each
   orthogonal-finite test it also gives entire `F` and `Fd` with the traces on these chambers and
   the identity `Fd(z, 1 - s) = Ph(z, s) F(z, s)`, where
   `Ph(z, s) = signA · ε(xs, ys)(s) · signM · ε(us, vs)(s + z)`. `Ph` never vanishes, since the
   signs are nonzero and `ε`-factors are units.
2. Uniform model membership gives continuity, the real gauge estimate and left
   `U`-invariance of `|V|` (`realUniformWhittakerRegularity`,
   `RealWhittakerGauge.exists_gauge_bound`). This holds for `W` and `B f` and, via
   `realUniformWhittakerCharacterDual`, for their duals. The real trace bound
   `exists_equalNormalizedTrace_bound` (from `RealLocalEqualChamberTrace`) then gives two
   estimates on vertical lines and compact exponent intervals beyond further thresholds:
   * for the primal normalized trace `P`, with multipliers `den(xs, ys)` and `den(us, vs)`;
   * for the dual normalized trace `Q`, with `den(xsd, ysd)` and `den(usd, vsd)`, the duals, and
     exponent `-z`.

   In both cases, differences between two tests are bounded by a continuous function of the
   difference of the tests, vanishing at zero, times `exp(K|Im s| + L|Im z|)`. The reciprocal
   `L`-factors are entire with strip growth (`ReciprocalEntire.entire`,
   `stripGrowth_realPairLFactor_denominator`).
3. `exists_tendsto_realOrthogonalFiniteSchwartz` gives orthogonal-finite tests `Φ_j → Ψ`. The real
   square Fourier transform is a composite of continuous linear maps, so `Φ̂_j → Ψ̂`. Let
   `F_j` and `Fd_j` be the functions for `Φ_j`.
4. On the lines `(v + s, s)` with `|Re v| ≤ R`, the differences `F_i - F_j` are uniformly small:
   * On a far right line `Re s = u`, the point `(v + s, s)` is in the primal chamber and the
     primal trace bound applies.
   * On a far left line `Re s = l`, write `F_j(z, s) = Ph(z, s)⁻¹ Fd_j(z, 1 - s)`. The point
     `(z, 1 - s)` is in the dual chamber, so the dual trace bound applies with exponent `-z`.
     The factor `|Ph(z, s)⁻¹|` is bounded there: `ε(w) = ε(0) |b|^(k w)`
     (`realPairEpsilon_eq_at_zero_mul_cpow`), so `|ε(w)⁻¹| ≤ |ε(0)|⁻¹ exp(|log |b|| k M)` when
     `|Re w| ≤ M` (`exists_norm_inv_realPairEpsilon_le`).

   The Library theorem `Langlands.Analysis.affineStripExtension` then gives a locally uniform
   limit `A`. It is holomorphic along holomorphic curves and has strip growth in `s`.
5. The primal trace of `A` follows from pointwise convergence and the primal trace bound
   (`F_j = P(Φ_j)` converges to `P(Ψ)`). For the dual trace,
   `Fd_j(z, s) = Ph(z, 1 - s) F_j(z, 1 - s)` converges both to `Ph(z, 1 - s) A(z, 1 - s)` and,
   via `Fd_j = Q(Φ̂_j)` on the dual chamber, to `Q(Ψ̂)(-z, s)`.

## Provenance and scope

This module is an internal real adaptation of the published complex module
`ComplexLocalEqualSquareLimit`, not a step of Jacquet's text. Its finite input comes from
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.2, pp. 56–58. There a compact
idempotent is applied to the `K_n`-finite square test `Φ₀`. This gives the finite product
expansion (8.2) of the unfolded integral and its reflected counterpart, which combine the
corank-one and matrix functional equations. That finite case is formalized in
`RealLocalEqualFiniteSquareNormalized` and `RealLocalEqualFiniteSquareChambers`.

The passage from orthogonal-finite square tests to all square Schwartz tests is the internal
limit argument implemented here, following the complex module: density of orthogonal-finite
tests, continuity of the square Fourier transform, uniform estimates on two vertical lines, the
Phragmén–Lindelöf extension `affineStripExtension`, and normalized traces. Jacquet uses related
continuity reductions with different scope. In §8.1, pp. 53–54, he reduces from general
Whittaker vectors and vector tests to `K_n`-finite and standard data. In §4.7, pp. 30–31, he
uses density of square tests for matrix-coefficient zeta integrals. Neither is the limit over
square tests in the unfolded integral used here. The real `ε`-factors depend on `s`, so the dual
side is stated with the reflection factor `Ph`, not with a constant phase. The inputs remain
conditional:

* the continuous Whittaker evaluation of `B`, an explicit hypothesis (the Library supplies it
  only for irreducible standard modules, under the Casselman–Wallach extension premise);
* the normalized corank-one equation for every larger coefficient;
* the normalized matrix equation for orthogonal-finite tests.

The module proves nothing about the actual equal-rank integral (the Jacquet expansion), and it
does not prove `RealLocalUniformPositiveEqualContinuationStatement`.
