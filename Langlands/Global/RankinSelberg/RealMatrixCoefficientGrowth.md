# The matrix normalized equation for real principal-series coefficients

Module `Langlands.Global.RankinSelberg.RealMatrixCoefficientGrowth`, namespace
`Langlands.Global.RankinSelbergGlobal.RealGodement`. Every declaration is proved, with no
axioms beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).

The module proves the open premise `RealMatrixCoefficientGrowthPremise t` of
`RealLocalEqualGrowthStep` at every rank `t`. As a consequence it removes that premise from the
reduction `realLocalUniformPositiveEqualContinuation_of_premises` of
`RealLocalUniformPositiveEqualContinuationStatement`.

## The premise

Put `m = t + 1`, `H = GL_{t+2}(ℝ)`, `ιT` the inverse transpose of `H`. Fix:

- real quotient data `D'` of rank `t + 1` (only its Haar measure `D'.groupHaar` on `H` is used);
- a nonzero real `a` and a parity `e`;
- a list `fs` of `t + 2` real character data, with block list `es = fs.map RealBlock.character`;
- a standard `K`-finite vector `f` of `es`, and a square Schwartz test `Ψ` whose left orthogonal
  translates span a finite-dimensional space.

`RealMatrixCoefficientGrowthPremise t` asserts `RealMatrixCoefficientNormalizedGrowth` (module
`RealLocalEqualFiniteSquareChambers`) for these data. That is: for every linear form `ℓ` on the
smooth position principal series of `RealPrincipalSeries.expand es` with
`HasCompactDerivativeBound`, write `b(g) = ℓ(π(g) f)` (`realStandardMatrixCoefficient`). Then

1. there is `β` such that for `Re w > β` the integrands
   `Ψ(g) sgn(det g)^e |det g|^(w + m/2) b(g)` and
   `Ψ̂(g) sgn(det g)^e |det g|^(w + m/2) b(ιT g)` are `D'.groupHaar`-integrable, where
   `Ψ̂ = realRectangularSchwartzFourier (-a) Ψ`;
2. the two matrix integrals `realWeightedMatrixIntegral D'.groupHaar e Ψ b` and
   `realWeightedMatrixIntegral D'.groupHaar e Ψ̂ (b ∘ ιT)` satisfy
   `RealJacquet.HasRealPairNormalizedGrowth` with lists `[character (charData e 0)]` and `es`,
   their blockwise duals, parameter `-a`, scale `√|a|` and sign `1`. So there are entire
   functions `N`, `Nd` of exponential growth on vertical strips, equal on a right half-plane to
   the two integrals multiplied by the reciprocal pair `L`-factors, with
   `Nd(1 - s) = ε(s, [charData e 0] × es, -a, √|a|) · N(s)` for every `s`.

## Declarations

- `expand_map_character cs`: `RealPrincipalSeries.expand (cs.map RealBlock.character)` is
  `cs.map RealBlock.character`. Each character block is its own single position, so the proof
  is induction on `cs` with a definitional unfolding of `expand` at a cons.
- `realDetCharacter_charData_zero_inverseTranspose e g`: the sign character `charData e 0` of the
  determinant takes the same value at `g` and at its inverse transpose. The Library's
  `realDetCharacter_inverseTranspose` gives the reciprocal value, and the value `z` satisfies
  `z · z = 1`, since `(x/|x|)² = 1` for `x = det g ≠ 0`.
- `realWeightedMatrixTest_mul_eq_zetaKernel e Ψ b w g`: the weighted integrand
  `realWeightedMatrixTest (charData e 0) Ψ (w + (t + 1)/2) g * b g` is the real matrix zeta kernel
  `GodementJacquet.realMatrixZetaKernel` (module `RealMatrixContinuation`) of the twisted
  coefficient `g ↦ realDetCharacter (charData e 0) g · b g` at `w`, for `GL_{t+2}(ℝ)`. Both are
  `Ψ(g) · sgn(det g)^e · b(g) · |det g|^(w + (t+1)/2)`, the power written once as a complex power
  and once through `detPower`.
- `hasRealPairNormalizedGrowth_list_congr` and `hasRealPairNormalizedGrowth_scale_congr`:
  `HasRealPairNormalizedGrowth` may be transported along an equality of the second list (with
  its dual list) and along an equality of scales, with the functions unchanged.
- `realMatrixCoefficientGrowth t : RealMatrixCoefficientGrowthPremise t`.
- `RealMatrixCoefficientGrowthStatement`: the proposition `∀ t, RealMatrixCoefficientGrowthPremise t`,
  proved by `realMatrixCoefficientGrowthStatement`.
- `RealLocalUniformPositiveEqualContinuationReducedPremisesStatement`: the implication
  `RealUniformPrincipalSeriesInclusionStatement → RealUniformCanonicalRangePremise →
  RealCanonicalStandardEvaluationPremise → (∀ t, RealJacquet.RealLocalAdjacentCharacterGrowthAtRank t) →
  RealLocalUniformPositiveEqualContinuationStatement`. It is proved by
  `realLocalUniformPositiveEqualContinuation_of_reducedPremises`, which applies the Library's
  `realLocalUniformPositiveEqualContinuation_of_premises` with `realMatrixCoefficientGrowth` as
  the matrix premise. The four remaining premises are not proved in this module.

## Proof of `realMatrixCoefficientGrowth`

Let `ℓ` be a compact-derivative-bounded form.

- The integrability clause is the Library's `exists_realWeightedMatrix_integrable` (module
  `RealMatrixCoefficientIntegrability`) for `D'.groupHaar`, the tests `Ψ` and `Ψ̂`.
- For the normalized clause apply `GodementJacquet.realMatrixPairNormalizedGrowth` (module
  `RealMatrixNormalizedGrowth`) at rank `n = t + 2` with:
  - the Haar measure `D'.groupHaar` and the Haar measure `Measure.haar` of the orthogonal group;
  - the block list `es` (of rank `t + 2` by `realRank_map_character`);
  - the section `expandedSmoothInclusion (t + 1) es f`, the form `ℓ`;
  - the character `d = charData e 0`, the test `Ψ` and the Fourier parameter `b = -a`.

  It gives `HasRealPairNormalizedGrowth` with lists `[character d]` and `expand es`, parameter
  `-a`, scale `√|-a|` and sign `1`, for `realMatrixZeta μ F Ψ` and
  `realMatrixZeta μ (F ∘ ιT) (matrixTransform (-a) Ψ)`, where
  `F(g) = realDetCharacter d g · ℓ(π(g) f) = sgn(det g)^e · b(g)`.
- `expand_map_character` replaces `expand es` by `es`, and `√|-a| = √|a|`.
- The functions agree everywhere, so `HasRealPairNormalizedGrowth.congr` applies:
  - primal: `realWeightedMatrixTest_mul_eq_zetaKernel` identifies the integrands;
  - dual: the same lemma for `b ∘ ιT`, together with
    `realDetCharacter_charData_zero_inverseTranspose` (so `F(ιT g) = sgn(det g)^e b(ιT g)`) and the
    Library's `matrixTransform_eq_realRectangularSchwartzFourier` (the trace-pairing transform
    `matrixTransform (-a) Ψ` is `realRectangularSchwartzFourier (-a) Ψ`).

The hypothesis on the left orthogonal span of `Ψ` is not used.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg` (PDF page = printed page), §4.7, pp. 30–31. For an
induced representation `I_{μ,u}` and a continuous linear form `λ`, the coefficient
`f(g) = λ(π_{μ,u}(g) φ)` satisfies, by Proposition 4.4 (p. 31), the functional equation (4.3)
`∫ Φ̂(g) f(g^ι) |det g|^{1-s+(n-1)/2} dg = γ(s, σ_u, ψ) ∫ Φ(g) f(g) |det g|^{s+(n-1)/2} dg`, and
on p. 30 the continued integral is a holomorphic multiple of `L(s, σ_u)` and is bounded at
infinity in vertical strips. The premise is a statement of this kind for the twist of `f` by the
sign character `sgn(det g)^e`, in the Library's normalization, with these differences:

- the coefficient forms are those with a compact derivative bound on the smooth position
  principal series, and the vectors are standard `K`-finite vectors, where Jacquet allows
  continuous forms on the smooth induced representation;
- the Fourier transform has a positive phase with parameter `-a` and its self-dual measure;
  Jacquet's negative phase for `ψ_a` is this transform at `-a`;
- the growth assertion is different. Jacquet states boundedness at infinity of the continued
  zeta integrals in vertical strips. Here the conclusion is `HasRealPairNormalizedGrowth`: the
  integrals multiplied by the reciprocal pair `L`-factors extend to entire functions of
  exponential growth on vertical strips, and these entire functions satisfy the normalized
  functional equation everywhere;
- the normalized functional equation is obtained in `RealMatrixNormalizedGrowth` from an
  explicit convolved Tate pair of determinant kernels (module `ArchimedeanDeterminantTheta`),
  not from Jacquet's argument with `K`-finite matrix coefficients and standard tests.

The module `RealMatrixNormalizedGrowth` proves the statement for the principal series of
`expand es`; this module specializes it to character lists and to the notation of
`RealLocalEqualFiniteSquareChambers`.
