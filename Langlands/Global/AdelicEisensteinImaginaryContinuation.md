# Eisenstein continuations holomorphic on the imaginary axis

Module `Langlands.Global.AdelicEisensteinImaginaryContinuation` states and
proves the proposition
`Langlands.Global.EisensteinImaginaryContinuationBridgeStatement`:

`EisensteinMeromorphicContinuationStatement.{0} →
EisensteinImaginaryAxisHolomorphyStatement →
EisensteinAbsoluteConvergenceStatement.{0} →
EisensteinImaginaryContinuationStatement`.

The four propositions are:

- `EisensteinMeromorphicContinuationStatement`, published in module
  `Langlands.Global.AdelicEisensteinContinuationStatement`
  (Bernstein–Lapid 2024, Theorem 2.3 (1) and the Corollary of §8.6). For an
  automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)` and `N > 0`, it gives a function
  `E'` on `X^*(P) ⊗ ℂ` that equals the Eisenstein series for `Re λ`
  sufficiently regular. In every linear coordinate system, near every point,
  `E'` is the underlying function of a meromorphic function with values in a
  Fréchet space `𝔉^R_L` of functions of uniform moderate growth.
- `EisensteinImaginaryAxisHolomorphyStatement`, published in module
  `Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement` (Lapid 2011,
  Proposition 6). For `φ ∈ A^2_P` and any continuation `E` of the Eisenstein
  series that is meromorphic in coordinates with domain `D`, it gives `E''`
  and `D' ⊇ i(X^*(P) ⊗ ℝ)` with `E''` meromorphic in coordinates with domain
  `D'` and `E'' = E` on `D ∩ D'`.
- `EisensteinAbsoluteConvergenceStatement`, published in module
  `Langlands.Global.AdelicEisensteinConvergenceStatement`
  (Mœglin–Waldspurger II.1.5). It gives a summable majorant of the terms of
  the Eisenstein series, uniform for `g` in a compact set and the parameter in
  a compact set of `R`-regular parameters.
- `EisensteinImaginaryContinuationStatement`, in module
  `Langlands.Global.AdelicSpectralTransformInputs`. It is one of the inputs of
  the reduction of `SpectralTransformStatement`. For finitely many
  `v j ∈ A^2_P` it asserts that there are functions `E j` and one set `D` with
  `IsEisensteinContinuation hK r hA hT v E D`: `D` contains
  `i(X^*(P) ⊗ ℝ)`, every `λ ↦ E j λ g` is meromorphic in coordinates with
  domain `D`, and for each `j` there is `R` with `E j λ = E(v j, λ)` for every
  `R`-regular `λ`.

The first and third premises are used at universe `0` because the conclusion
quantifies number fields `F : Type`. The bridge is a theorem about these four
Library propositions. It claims nothing about whether its premises hold; none
of them is proved in the Library, and their proofs are separate tasks.

## Provenance

The bridge is internal to the Library. It connects published statements about
Eisenstein series with the input `EisensteinImaginaryContinuationStatement`
of the reduction of the spectral transform (task
`Langlands.Global.SpectralTransformStatement`; Arthur 2005, Theorem 7.2 (b);
Getz–Hahn (10.22)–(10.24)). Mathematically, the conclusion combines
Bernstein–Lapid, Theorem 2.3 (1) with Lapid 2011, Proposition 6, as the
docstring of the Inputs module says. The Lean statements differ in form, and
the bridge handles four points.

1. The continuation of `EisensteinMeromorphicContinuationStatement` is
   meromorphic locally, with values in Fréchet spaces that depend on the
   point. The holomorphy statement and the conclusion need scalar functions
   `λ ↦ E λ g` that are meromorphic with one domain `D` for all `g`. The
   bridge glues the local data (`exists_glued_eisensteinContinuation`). The
   domain is the set of points near which all the scalar functions are
   holomorphic.
2. `EisensteinMeromorphicContinuationStatement` needs `N > 0`. For `N = 0`,
   `G(𝔸)` is trivial and the Eisenstein series is entire.
3. The holomorphy statement returns a representative `E''` that agrees with
   the Eisenstein series only on part of the regular region. The conclusion
   needs agreement on all of an `R`-regular region. The bridge redefines the
   continuation on the regular region, keeping a domain that contains
   `i(X^*(P) ⊗ ℝ)`.
4. If no root of `A` occurs in the unipotent radical, every parameter is
   regular, so point 3 would require the Eisenstein series itself to be
   meromorphic. Here the convergence statement makes the series continuous
   everywhere, and continuity forces it to agree with `E''` on `D'`.

Meromorphy in coordinates needs `X^*(P) ⊗ ℂ` to be finite-dimensional. This
is proved in module `Langlands.GroupScheme.Rational.ParabolicCharacterLattice`,
so the bridge needs no premise for it.

## Declarations

### Evaluation (section `Evaluation`)

- `uniformGrowthEvalCLM g`: evaluation at `g ∈ G(𝔸)` as a continuous linear
  form on the Fréchet space `𝔉^R_L` (`UniformGrowthFrechetSpace`, for
  `N > 0`). The value `f(g)` is the weighted derivative of order `1` of `f`,
  an element of `ℓ^∞(G(𝔸))`, evaluated at `g` and multiplied by `‖g‖^R`.
  Here `‖g‖` is the adelic norm `adelicSourceNorm` of the matrix
  representation, which is positive. The weighted derivative is continuous
  for the initial topology of `𝔉^R_L`, and evaluation on `ℓ^∞` is continuous
  (`lp.evalCLM`).

### Parameters (section `Parameters`)

- `parameterRealPart_imaginaryParameter`: `Re(i x) = 0` for
  `x ∈ X^*(P) ⊗ ℝ`. Proved by induction on tensors.
- `finiteDimensional_complexCharacterParameter`: for a presented parabolic
  of a connected reductive group, `X^*(P) ⊗ ℂ` is finite-dimensional over
  `ℂ`. `X^*(P)` is a finite `ℤ`-module
  (`ParabolicRootPresentation.rationalCharacters_free_finite`), and base
  change preserves finiteness.
- `isRegularParameter_mono`: `R'`-regular parameters are `R`-regular for
  `R ≤ R'`.
- `isOpen_preimage_regularityForm_lt`: for a root `α` of `A`, a real `R` and
  coordinates `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`, the set of `s` with
  `B(Re (e s)|_A, α) < R` is open. The map
  `s ↦ B(Re (e s)|_A, α)` is a composite of `ℝ`-linear maps
  (`weylInducedCharacterForm`, `realParameterRestriction`,
  `parameterRealPart`, `e`), hence continuous on `ℂⁿ`.

### The series (section `Series`)

- `differentiable_eisensteinTerm`: for every coset `c ∈ P(F) \ G(F)` and
  every `g`, the term `φ(γ_c g) exp⟨e s, H_P(γ_c g)⟩` of the Eisenstein
  series (`IsIwasawaCompact.eisensteinTerm`) is an entire function of
  `s ∈ ℂⁿ`, because `s ↦ ⟨e s, H⟩` is `ℂ`-linear.
- `differentiable_eisensteinSeries_of_subsingleton`: if `G(𝔸)` has one
  element, then `P(F) \ G(F)` has one element, the series is its single term
  (`tsum_eq_single`), and it is entire in `s`.
- `subsingleton_adelicGroupPoints_of_rank_zero`: if `rho` is a closed
  embedding of `G` into `GL_0`, then `G(𝔸)` has at most one element. The
  adelic matrix map of a closed subgroup is injective
  (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`), and its target,
  the units of the `0 × 0` adelic matrices, has one element.

### One form (section `PerForm`)

- `exists_glued_eisensteinContinuation`: let `N > 0` and let `φ` be an
  automorphic form on `U(𝔸)M(F) \ G(𝔸)`, the hypothesis of
  `EisensteinMeromorphicContinuationStatement`. Then there are `E'`, a set
  `D₀` and a real `R₀` such that `E' λ` is the Eisenstein series for every
  `R₀`-regular `λ`, and every `λ ↦ E' λ g` is meromorphic in coordinates with
  domain `D₀`. Proof: take `E'` and `R₀` from the premise. Fix the coordinates
  `e₀ : ℂᵐ ≃ X^*(P) ⊗ ℂ` of a basis. At each `s₀ ∈ ℂᵐ`, the premise gives an
  open `W ∋ s₀` and a meromorphic `f : W → 𝔉^R_L` with domain `D` whose
  values on `D` have underlying functions `E'(e₀ s)`. Evaluation at the
  points `g` (`uniformGrowthEvalCLM g`) gives local meromorphic data at `s₀`
  for the family `(s ↦ E'(e₀ s)(g))_g`
  (`hasLocalMeromorphicData_of_isMeromorphicOn`). The denominator does not
  depend on `g`. Gluing (`exists_isMeromorphicOn_of_local`) gives one domain
  `U₀ ⊆ ℂᵐ` for all `g`. Put `D₀ = e₀(U₀)` and pass to all coordinate systems
  (`isMeromorphicInCoordinatesOn_of_coordinates`). The cited lemmas are in
  module `Langlands.Analysis.Meromorphic.CoordinateGluing`.
- `continuous_eisensteinSeries_of_unipotentRoots_eq_empty`: if
  `r.unipotentRoots = ∅`, then for every `g` and coordinates `e` the function
  `s ↦ E(φ, e s)(g)` is continuous on `ℂⁿ`. Every parameter is `R`-regular
  for every `R`. So for each `s₀` the convergence statement, applied to
  `C = {g}` and the closed unit ball `Λ` around `s₀`, gives a summable
  majorant of the terms on `Λ`. The terms are continuous
  (`differentiable_eisensteinTerm`), so the series is continuous on `Λ`
  (Mathlib's `continuousOn_tsum`), hence at `s₀`.
- `exists_imaginary_eisensteinContinuation`: for `φ ∈ A^2_P` there are `E`
  and `D` with `i(X^*(P) ⊗ ℝ) ⊆ D`, every `λ ↦ E λ g` meromorphic in
  coordinates with domain `D`, and some `R` with `E λ = E(φ, λ)` for every
  `R`-regular `λ`. The proof distinguishes three cases.
  - `N = 0`. `G(𝔸)` is trivial, and the Eisenstein series is entire in every
    coordinate system. Take `E` the Eisenstein series, `D` the whole space
    (`isMeromorphicInCoordinatesOn_univ`) and `R = 0`.
  - `N > 0`. Elements of `A^2_P` are automorphic forms on
    `U(𝔸)M(F) \ G(𝔸)`, so `exists_glued_eisensteinContinuation` gives
    `(E', D₀, R₀)`. The holomorphy statement, applied to `(E', D₀)`, gives
    `E''` and `D' ⊇ i(X^*(P) ⊗ ℝ)` with `E''` meromorphic in coordinates with
    domain `D'` and `E'' = E'` on `D₀ ∩ D'`.
    - No root of `A` in the unipotent radical. Every parameter is regular,
      so `E'` is the Eisenstein series everywhere. Take `E` the Eisenstein
      series, `D = D'` and `R = 0`. In the coordinates `e₀`, the series is
      continuous (previous lemma), `E''` is continuous on the open set
      `e₀⁻¹(D')`, and the two agree on `e₀⁻¹(D' ∩ D₀)`. That set is dense in
      `e₀⁻¹(D')` because `e₀⁻¹(D₀)` is dense. So they agree on `e₀⁻¹(D')`
      (`Set.EqOn.of_subset_closure`). Hence the series is meromorphic in
      coordinates with domain `D'` (`IsMeromorphicInCoordinatesOn.congr_mono`).
    - A root `α₀` of `A` in the unipotent radical. Put
      `R₁ = max R₀ 0 + 1`, so `R₀ ≤ R₁` and `R₁ > 0`, and
      `O = {λ | B(Re λ|_A, α₀) < R₁}`. Define `E λ` to be the Eisenstein
      series if `λ` is `R₁`-regular and `E'' λ` otherwise. Put
      `D = D' ∩ (D₀ ∪ O)` and `R = R₁`. Then `E` is the Eisenstein series on
      `R₁`-regular parameters by definition. An imaginary parameter lies in
      `D'`, and lies in `O` because its real part is `0` and `R₁ > 0`. The set
      `D` is open and dense in coordinates (`D'` and `D₀` are, and `O` is
      open in coordinates by `isOpen_preimage_regularityForm_lt`). For
      `λ ∈ D`, `E λ = E'' λ`: if `λ` is `R₁`-regular, then
      `B(Re λ|_A, α₀) > R₁`, so `λ ∉ O` and `λ ∈ D₀`. Then
      `E λ = E(φ, λ) = E' λ = E'' λ`, the middle equality because `λ` is
      `R₀`-regular (`isRegularParameter_mono`). Otherwise `E λ = E'' λ` by
      definition. So `E` is meromorphic in coordinates with domain `D ⊆ D'`
      (`IsMeromorphicInCoordinatesOn.congr_mono`).

### The bridge

`EisensteinImaginaryContinuationBridgeStatement` is the implication displayed
above. Its proof `eisensteinImaginaryContinuationBridge` takes the data of
`EisensteinImaginaryContinuationStatement`. It derives that `P` is locally of
finite type, as the statement does, and applies
`exists_imaginary_eisensteinContinuation` to each `v j`. This gives `E j`,
`D j` and `R j`. The common domain is `D = ⋂ j, D j`, which contains
`i(X^*(P) ⊗ ℝ)` and is open and dense in coordinates as a finite
intersection (`isOpenDenseInCoordinates_iInter`). Each `E j` is meromorphic in
coordinates with the smaller domain `D` (`IsMeromorphicInCoordinatesOn.congr_mono`).
For `k = 0`, `D` is the whole space and the conditions are vacuous.

The proof is a direct Lean proof. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.
