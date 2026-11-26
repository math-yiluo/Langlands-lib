# Eisenstein series along a complex line of parameters

Module `Langlands.Global.AdelicEisensteinLineContinuation` (namespace
`Langlands.Global.EisensteinLine`) restricts the meromorphic continuation of group-scheme
Eisenstein series to a complex line `s ↦ s λ₁` of parameters. It proves:

- one function `E(s, g)` that is the Eisenstein series for `Re s` large;
- near every point, a power of `s - s₀` that makes `E` jointly continuous, holomorphic in `s` and
  left `G(F)`-invariant;
- no power at points where every continuation of the series agrees with one that is holomorphic
  there.

Everything is stated for number fields `F : Type u` in an arbitrary universe, from the two premises
`EisensteinMeromorphicContinuationStatement.{u}` and `EisensteinJointRootHyperplaneStatement.{u}`.
The module does not prove either premise.

## Setting

Throughout, `G` is a connected reductive group over `F` and `p : P → G` a parabolic with geometric
unipotent radical `iU : U → P` and rational Levi `l : M → P`, presented through the split component
`a : A → M` by `r : ParabolicRootPresentation p l a`. `K` is a maximal compact subgroup with
Iwasawa height (`hK : IsIwasawaCompact p K`), `rho` a closed matrix embedding with `N > 0`, and
`φ` an automorphic function on `U(𝔸) M(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for
`parabolicQuotientSubgroup`). These are the hypotheses of the two premises.
`hK.eisensteinSeries φ λ` is the Library's unconditional Eisenstein sum
`∑_{γ ∈ P(F)\G(F)} φ(γ g) exp ⟨λ, H_P(γ g)⟩`.

## Main results

**`exists_lineContinuation`.** Let `λ₁ ∈ X^*(P) ⊗ ℂ` satisfy:

- (root forms) `r.rootFunctional hA hT β λ₁ ≠ 0` for every root `β` of `A` in the unipotent
  radical (`r.unipotentRoots`);
- (regularity) for every `R` there is `σ` such that `s λ₁` is `R`-regular
  (`r.IsRegularParameter`) whenever `σ < Re s`.

Let `Z ⊆ X^*(P) ⊗ ℂ` be such that every continuation `E₀` of the series has a second continuation
holomorphic on `Z`. Here a continuation is a function `E₀` that is meromorphic in coordinates with
one domain of holomorphy `D` for all `g` and equals `hK.eisensteinSeries φ` for `Re λ` sufficiently
regular. The second continuation `E₁` has a domain `D' ⊇ Z` and agrees with `E₀` on `D ∩ D'`.
Assume both premises in the universe of `F`. Then there are `E : ℂ → G(𝔸) → ℂ` and `σ : ℝ` with:

1. `E s = hK.eisensteinSeries φ (s • λ₁)` for `σ < Re s`;
2. for every `s₀ ∈ ℂ` there are `m : ℕ`, an open `W ∋ s₀` and `h : ℂ → G(𝔸) → ℂ` such that
   - `h` is continuous on `W × G(𝔸)`;
   - `s ↦ h s g` is complex differentiable on `W` for every `g`;
   - `h s (c g) = h s g` for `s ∈ W` and `c ∈ G(F)` (`rationalSubgroup F G`);
   - `h s g = (s - s₀)^m E s g` for `s ∈ W`, `s ≠ s₀`;
   - if `s₀ λ₁ ∈ Z`, then `m = 0` and `h s₀ = E s₀`.

**`HasImaginaryAxisHolomorphy r hA hT hK φ`** (a definition) is this hypothesis on `Z` for
`Z = i(X^*(P) ⊗ ℝ)`, the range of `imaginaryParameter`. It is word for word the conclusion of
`EisensteinImaginaryAxisHolomorphyStatement` (Lapid 2011, Proposition 6) for the form `φ`.
**`exists_lineContinuation_imaginary`** is the corresponding form of `exists_lineContinuation`.
Its last clause reads: if `HasImaginaryAxisHolomorphy` holds and `s₀ λ₁` is imaginary, then `m = 0`
and `h s₀ = E s₀`.

**`hasImaginaryAxisHolomorphy_of_eq_mul_heightPower`.** If `φ = ψ · m_P^{iy}`, that is
`φ x = ψ x · hK.heightPower (imaginaryParameter F P y) x` for all `x` and a real parameter `y`,
and `ψ` has `HasImaginaryAxisHolomorphy`, then so has `φ`. The proof only translates parameters,
so this step needs no assumption on the universe of `F`.

## Implemented proof

*Gluing* (`exists_glued_continuation`). The first premise gives, near every point and in every
linear coordinate system, a meromorphic function with values in a Fréchet space `𝔉^R_L` of
functions of uniform moderate growth. Evaluation at `g ∈ G(𝔸)` is a continuous linear form
(`UniformGrowthFrechetSpace.evalCLM`). The Library's gluing lemmas
`hasLocalMeromorphicData_of_isMeromorphicOn` and `exists_isMeromorphicOn_of_local` (module
`Langlands.Analysis.Meromorphic.CoordinateGluing`) give one continuation `E'` with one domain of
holomorphy `D₀` for all `g`, and `E' = hK.eisensteinSeries φ` on `R₀`-regular parameters. The
argument is that of `exists_glued_eisensteinContinuation` in
`Langlands.Global.AdelicEisensteinImaginaryContinuation`, which is stated for `F : Type`; here it is
written for `F : Type u`.

*Continuity of the series* (`continuousOn_eisensteinSeries_of_bound`). The Library's
`eisensteinAbsoluteConvergence` gives `Rc` and summable majorants of the terms on compact sets of
`Rc`-regular parameters. The terms are entire in coordinates (`differentiable_eisensteinTerm`).
The `Rc`-regular parameters form an open set (`isOpen_setOf_isRegularParameter`), and every point
of it has a closed ball inside it. So the series is continuous in coordinates on that set
(`continuousOn_tsum`).

*The line* (`exists_lineContinuation`). Fix coordinates `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and
`v = e⁻¹ λ₁`. Put `Rs = max R₀ Rc` and let `σ` be a threshold beyond which `s λ₁` is `Rs`-regular.
Let `(E'', D'')` be the second continuation given by the hypothesis on `Z` for `(E', D₀)`.

The second premise, applied to `E'` and `D₀`, gives at every center `z₀ ∈ ℂⁿ` the following data:
a finite set `S` of roots in the unipotent radical, an exponent `m`, an open `W' ∋ z₀`, and `H`
continuous on `W' × G(𝔸)`, holomorphic in `z` and left `G(F)`-invariant, with `H z g = Q(z) E'(e z) g`
whenever `e z ∈ D₀`, where `Q(z) = (∏_{β ∈ S} B(e z - e z₀, β))^m`. All values on the line are read
off the quotients `H / Q` by one density argument (`eqOn_of_dense`). Let `O` be an open set and
`f` a function continuous on `O` with `f = E'(e ·) g` on `O ∩ e⁻¹ D₀`. Then `H / Q = f` on
`O ∩ W' ∩ {Q ≠ 0}`, because `e⁻¹ D₀` is dense. Applied to the right `f`, this shows:

- the quotients of two centers agree where both are defined;
- a quotient equals the Eisenstein series at `Rs`-regular points;
- a quotient equals `E''` on `e⁻¹ D''`;
- the series equals `E''` on `Rs`-regular points of `e⁻¹ D''`.

`E s g` is defined as follows:

- the series at `s λ₁` if `σ < Re s`;
- otherwise `E''(s λ₁) g` if `s λ₁ ∈ D''`;
- otherwise the quotient at `s v` of any center whose quotient is defined there;
- `0` if there is none.

Clause 1 holds by definition. At a center `z₀ = s₀ v`, the root forms are linear and nonzero at
`λ₁`. So `Q(s v) = (s - s₀)^k κ^m` with `k = |S| m` and `κ = ∏_{β ∈ S} B(λ₁, β) ≠ 0`. If
`s₀ λ₁ ∉ Z`, then `h s g = κ^{-m} H(s v, g)` on `W = {s : s v ∈ W'}` satisfies clause 2 with
exponent `k`, by the agreements above.

If `s₀ λ₁ ∈ Z ⊆ D''`, then `f(s, g) = E''(s λ₁) g` is holomorphic in `s` on
`W₁ = {s : s v ∈ W' ∩ e⁻¹ D''}`. On `W₁ \ {s₀}` it equals `κ^{-m} (s - s₀)^{-k} H(s v, g)`, so it is
jointly continuous there. `Langlands.Analysis.exists_ball_continuousOn_of_punctured` (the Cauchy
integral formula) makes `f` jointly continuous on a disc around `s₀`. Left invariance at `s₀` itself
follows by continuity in `s` from the invariance at nearby `s ≠ s₀`. On the disc, `E = f`, also at
`s₀`. So `m = 0` and `h = f`.

*Imaginary twists.* `eisensteinSeries_of_eq_mul_heightPower` shows: if `φ = ψ m_P^c`, then
`E(φ, λ) = E(ψ, λ + c)` termwise, because `exp ⟨λ + c, H⟩ = exp ⟨λ, H⟩ exp ⟨c, H⟩`. An imaginary `c`
does not change `Re λ`, so it does not change regularity (`isRegularParameter_add_imaginaryParameter`).
Meromorphy in coordinates is invariant under translations (`isMeromorphicOn_comp_add_const`,
`isMeromorphicInCoordinatesOn_comp_add_const`). For a continuation `E₀` of the series of `φ`,
`λ ↦ E₀(λ - c)` is a continuation of the series of `ψ`. Its second continuation, translated back by
`c`, is the required continuation for `φ`. Its domain contains the imaginary parameters, because
`c = iy` is imaginary and the imaginary parameters form a real subspace.

## Provenance

- The two premises are Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
  J. Amer. Math. Soc. 37 (2024), Theorem 2.3 (1) and (6) (p. 191), with the Fréchet formulation
  of the Corollary in §8.6. The restriction to a line uses no further input from the source.
- The continuity of the series for regular parameters is the absolute and locally uniform
  convergence of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  II.1.5, Proposition (pp. 85–86), as formalized in `EisensteinAbsoluteConvergenceStatement` and
  proved in the Library.
- `HasImaginaryAxisHolomorphy` is the conclusion of Lapid, *On Arthur's asymptotic inner product
  formula of truncated Eisenstein series* (Clay Math. Proc. 13, 2011), Proposition 6 (p. 329),
  in the form of `EisensteinImaginaryAxisHolomorphyStatement`.
- The twist `φ = ψ m_P^{iy}` is a term of Lapid's decomposition (1) of an element of `A_P`
  (§2, p. 311), `ϕ(g) = ∑_i e^{⟨λ_i, H_P(g)⟩} Q_i(H_P(g)) ψ_i(g)` with `ψ_i ∈ A^n_P`, for one
  imaginary exponent `λ = iy` and `Q = 1`.
