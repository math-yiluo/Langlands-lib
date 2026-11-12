# Functional equation of Eisenstein series

Module `Langlands.Global.AdelicEisensteinFunctionalEquationStatement` states
`Langlands.Global.EisensteinFunctionalEquationStatement` as a proposition
definition. It supplies no proof.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3 (4), journal p.191 (PDF page 5): for any `w ∈ W(P, Q)`,
  `E(M(w, λ)φ, wλ) = E(φ, λ)` for `λ ∈ 𝔛_P`, as an identity of the
  meromorphic continuations of Theorem 2.3 (1) and (3).
- §2.1, p.190: `W(P, Q)` is the set of cosets `wM_P(F)` with `w ∈ G(F)` and
  `wM_Pw⁻¹ = M_Q`; each induces a linear isomorphism `𝔞_P → 𝔞_Q`.

Only the number field case is stated.

## Statement

The data are those of the Eisenstein and intertwining statements
(modules `Langlands.Global.AdelicEisensteinConvergenceStatement`,
`Langlands.Global.AdelicIntertwiningOperator` and
`Langlands.Global.AdelicIntertwiningContinuationStatement`), with `Q`
standard as well:

- `G` connected reductive over a number field `F`;
- `P = MU` with presentation `r : ParabolicRootPresentation p l a`, `iU` a
  geometric unipotent radical of `P`;
- `Q = M'V` with its own presentation
  `r' : ParabolicRootPresentation q l' a'`, `q` a closed immersion, `Q` and
  `V` affine, `iV` a geometric unipotent radical of `Q`, `iV ≫ q` a closed
  immersion; the presentation makes `q` parabolic and `l'` a rational Levi;
- `π' : Q → M'` with `l' ≫ π' = 𝟙 M'` (the Levi projection);
- `(w, c)` with `IsWeylConjugation p l q l' w c`: `w ∈ G(F)`, `c : M' → M`
  an isomorphism with `l(c(m')) = w⁻¹ l'(m') w`, so `wMw⁻¹ = M'` and `w`
  represents an element of BL's `W(P, Q)`;
- `K` maximal compact in `G(𝔸)` with `P(𝔸)K = G(𝔸)` (`hK`) and
  `Q(𝔸)K = G(𝔸)` (`hK'`), a closed matrix embedding `rho`, the
  smooth-structure data `hsmooth`, `hcalc`, and `φ ∈ 𝒜_P`
  (`IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F p iU l` and
  the archimedean part `K.comap (ofInfinite F G)` of `K`).

The statement is universal in the continuations. It quantifies

1. `EP : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and `DP` such that for every `g` the
   scalar function `λ ↦ EP λ g` is meromorphic with domain of holomorphy
   `DP` (`IsMeromorphicInCoordinatesOn`, module
   `Langlands.Analysis.Meromorphic.LinearCoordinates`), and for some `R`,
   `EP λ = hK.eisensteinSeries φ λ` whenever
   `r.IsRegularParameter hA hT R λ`;
2. `k`, `ψ : Fin k → (G(𝔸) → ℂ)`, `coeff : Fin k → (X^*(P) ⊗ ℂ → ℂ)` and
   `D` such that every `ψ i ∈ 𝒜_Q` (`IsAutomorphicFunctionOn` for
   `parabolicQuotientSubgroup F q iV l'`), every `coeff i` is meromorphic
   with domain `D`, and for some `R`,
   `hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g`
   for every `g` whenever `λ` is `R`-regular;
3. `EQ : Fin k → X^*(Q) ⊗ ℂ → (G(𝔸) → ℂ)` and `DQ` such that every
   `μ ↦ EQ i μ g` is meromorphic with domain `DQ`, and for each `i` there is
   `R` with `EQ i μ = hK'.eisensteinSeries (ψ i) μ` whenever
   `r'.IsRegularParameter hA' hT' R μ`.

The conclusion: for every `λ ∈ DP ∩ D` with `wλ ∈ DQ` and every `g ∈ G(𝔸)`,

`EP λ g = ∑ i, coeff i λ * EQ i (wλ) g`,

where `wλ = weylParameter l c π' λ` (`χ ↦ χ ∘ l ∘ c ∘ π'`).

## Correspondence with the source

- The left side of BL's identity. By Theorem 2.3 (3), `M(w, λ)φ` takes
  values in a finite-dimensional subspace of `𝒜_Q`, spanned by some
  `ψ i`, with meromorphic coefficients `coeff i` (see the Markdown of the
  intertwining continuation statement). Since `E(·, μ)` is linear on
  `𝒜_Q`, `E(M(w, λ)φ, wλ) = ∑ i, coeff i λ · E(ψ i, wλ)`, the right side of
  the conclusion. BL's right side `E(φ, λ)` is `EP`.
- Universal form. Instead of naming the continuations, the statement
  applies to all meromorphic functions that agree with the convergent
  series and integrals on regions `Re λ ≫ 0`. Such data exist by
  Theorem 2.3 (1) and (3) (for (1), evaluating BL's `𝔉_umg`-valued
  continuation at `g` is continuous, so it gives scalar meromorphic
  functions; for (3), the intertwining continuation statement). Any two
  choices agree on the intersection of their domains: their difference is
  holomorphic there, locally a quotient `h/g` with `g ≢ 0` on a connected
  open set, and vanishes on the nonempty open regular region; the set of
  points near which it vanishes is therefore open and closed in `ℂⁿ`. So
  for the true continuations the conclusion is BL's identity, and for any
  other choice it follows from BL's identity on a dense open subset of
  `DP ∩ D ∩ w⁻¹DQ` by continuity. This is explanatory and not proved here.
- `wλ`. `weylParameter l c π'` is the composite of the isomorphisms
  `X^*(P) ≅ X^*(M)` (restriction along `l`; characters are trivial on `U`),
  `c^* : X^*(M) ≅ X^*(M')` and `X^*(M') ≅ X^*(Q)` (composition with `π'`),
  after `⊗ ℂ`; so it is BL's linear isomorphism `w : 𝔛_P → 𝔛_Q`, and
  `w⁻¹DQ` is open and dense. It does not depend on the retraction `π'`.
- Regions. "`⟨Re λ, α^∨⟩ ≫ 0` for `α ∈ Δ_P`" is
  `r.IsRegularParameter hA hT R λ` for some `R`, as explained in the
  Markdown of the Eisenstein convergence statement; likewise for `Q` with
  `r'`. The presentations `r` and `r'` need not use the same maximal split
  torus or minimal parabolic. BL take `P` and `Q` standard with respect to
  one minimal parabolic; a rational conjugation reduces the general case to
  theirs, as in the Markdown of the intertwining continuation statement.
- Where both sides are not holomorphic nothing is claimed; BL's identity of
  meromorphic functions is equivalent to equality on a dense open set.
- The compact subgroup. BL (§2.1) fix `K` in good position with respect to a
  minimal Levi `M₀`; here `K` is any maximal compact subgroup with
  `P(𝔸)K = Q(𝔸)K = G(𝔸)`. The reduction is the one described in the
  Markdown of the Eisenstein convergence statement. In the functional
  equation the normalization `m_Q^{-wλ}` of `M(w, λ)φ` cancels against
  `m_Q^{wλ}` in `E(·, wλ)`, so only `m_P` depends on `K`.

## Scope

The existence of the continuations (BL 2.3 (1), (3)) is not part of this
statement; it is stated separately in
`Langlands.Global.EisensteinMeromorphicContinuationStatement` and
`Langlands.Global.IntertwiningMeromorphicContinuationStatement`. The cocycle
relation (2.3 (5)) and the location of singularities (2.3 (6)) are not
stated here.
