# Reduction of the meromorphic continuation of intertwining operators

Module `Langlands.Global.AdelicIntertwiningContinuationReduction`, written by Worker 979 for
Task 5501 (`c1648848-1e63-45a5-8590-3e61a11b64f1`). That task's target is the Library's
`Langlands.Global.IntertwiningMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicIntertwiningContinuationStatement`). It is Bernstein–Lapid,
Theorem 2.3 (3), number field case.

This module states two results, each with its own source, and proves that together they imply
the target. It proves neither of them. All declarations are in the namespace
`Langlands.Global`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), 187–234. It is registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; locators below are journal pages of
the PDF in that folder, with the TeX file `1911.02342.tex` for line numbers.

- Theorem 2.3 (3), p. 191 (TeX lines 458–460): "For any `w ∈ W(P, Q)`, the map
  `λ ↦ M(w, λ)φ`, taking values in a finite-dimensional linear subspace of `𝒜_Q`, admits a
  meromorphic continuation to `𝔛_P`."
- §8.2, the Lemma following "The following is a standard consequence of Harish-Chandra's
  finiteness theorem", p. 222 (TeX lines 3274–3290): "For any `φ ∈ 𝒜_P` and `w ∈ W(P, Q)` the
  automorphic forms `M(w, λ)φ`, whenever defined, belong to a finite-dimensional linear subspace
  of `𝒜_Q` (independently of `λ`)."
- §8.5, *Meromorphic continuation of intertwining operators*, pp. 224–225 (TeX lines
  3417–3486). It ends with the formula
  `M(w, λ)φ = D̃(λ)⁻¹ (D(λ)((C_{G,Q} E(φ, λ))_{-wλ}))` and the sentence "this provides
  meromorphic continuation of `M(w, λ)φ`".
- §3.1, p. 192, for holomorphic and meromorphic functions with values in a locally convex
  space. The Library's `IsHolomorphicOn` and `IsMeromorphicOn` formalize this.

## Common setting

Both statements carry exactly the binders and hypotheses of
`IntertwiningMeromorphicContinuationStatement`, in the same order:

- a number field `F`;
- a connected reductive `G`;
- a parabolic `p : P → G` with unipotent radical `iU`, rational Levi `l : M → P` and presentation
  `r`;
- a parabolic `q : Q → G`, a closed immersion, with unipotent radical `iV`, rational Levi
  `l' : M' → Q` with `Q = M' ⋉ V`, and a retraction `π'` (`l' ≫ π' = 𝟙 M'`);
- a pair `(w, c)` with `IsWeylConjugation p l q l' w c`;
- a maximal compact `K` with `hK : IsIwasawaCompact p K` and `hK' : IsIwasawaCompact q K`;
- a closed matrix embedding `rho`, the data `hsmooth` and `hcalc`;
- `φ` with `IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
  (K.comap (ofInfinite F G).toMonoidHom) rho φ`, i.e. `φ ∈ 𝒜_P`.

`hK.intertwiningOperator hK' iU l iV c π' w φ λ : G(𝔸) → ℂ` is the Library's
`M(w, λ)φ = m_Q^{-wλ} · ∫ φ_λ(w⁻¹ v ·) dv` (module `Langlands.Global.AdelicIntertwiningOperator`).
"`λ` is `R`-regular" means `r.IsRegularParameter hA hT R λ`, the region of the convergence
statements. The Markdown of the target statement explains the following points, which apply
unchanged here:

- why this region lies in the region where the intertwining integral converges;
- why `Q` need not be standard;
- why `K` need not be in good position;
- how `π'` gives BL's `wλ`.

## Statement: `IntertwiningFiniteSpanStatement`

In the common setting, there are `k : ℕ`, functions `ψ : Fin k → G(𝔸) → ℂ` and a real `R₀` such
that:

- every `ψ i` satisfies `IsAutomorphicFunctionOn F G hsmooth hcalc
  (parabolicQuotientSubgroup F q iV l') (K.comap (ofInfinite F G).toMonoidHom) rho`, i.e.
  `ψ i ∈ 𝒜_Q` (an automorphic form on `V(𝔸)M'(F) \ G(𝔸)`);
- for every `R₀`-regular `λ`,
  `hK.intertwiningOperator hK' iU l iV c π' w φ λ ∈ Submodule.span ℂ (Set.range ψ)`. Here the
  span is taken in the complex vector space of all functions `G(𝔸) → ℂ`.

Correspondence with BL's Lemma in §8.2. A finite-dimensional subspace of `𝒜_Q` has a finite
basis consisting of elements of `𝒜_Q`. Conversely, the span of finitely many elements of `𝒜_Q`
is a finite-dimensional subspace of `𝒜_Q`. So the existence of the `ψ i` is BL's conclusion. BL's
"whenever defined" refers to the values of `λ` where `M(w, λ)φ` is given by its convergent
integral. The statement uses the region `R₀`-regular inside that domain, as all the Library's
statements about `M(w, λ)` do. Outside its domain the Library's operator is the integral with
value `0` where the integrand is not integrable, and nothing is asserted there. BL deduce the
Lemma as follows:

1. Fix an idempotent `e` in the algebra of finite functions on `K` with `δ(e)φ = φ`. The
   intertwining integral commutes with right translation by `K`, so the same `e` fixes
   `M(w, λ)φ` whenever it is defined. This bounds the `K`-types of `M(w, λ)φ` uniformly in `λ`.
2. A finite-codimensional ideal `I` of the centre `𝔷^M` annihilates
   `m ↦ δ_P(m)^{-1/2} φ(mg)` for all `g`. Its conjugate `wI` annihilates the corresponding
   function for `M(w, λ)φ` on `M_Q(𝔸)`. This gives a finite-codimensional ideal of the centre `𝔷`
   of the enveloping algebra, independent of `λ`, that annihilates `M(w, λ)φ`.
3. Harish-Chandra's finiteness theorem then gives the finite-dimensional space.

## Statement: `IntertwiningWeakMeromorphicContinuationStatement`

In the common setting, there are `E : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)`, a set
`D ⊆ X^*(P) ⊗ ℂ` and a real `R₀` with two properties:

- `IsMeromorphicInCoordinatesOn E D`. The target space `G(𝔸) → ℂ` of all functions carries
  Mathlib's product topology, the topology of pointwise convergence.
- `E λ = hK.intertwiningOperator hK' iU l iV c π' w φ λ` for every `R₀`-regular `λ`.

Meaning. A continuous linear form on `G(𝔸) → ℂ` with the product topology is a finite linear
combination of point evaluations. So, in every linear coordinate system on `X^*(P) ⊗ ℂ`, the
statement says three things:

- `D` is open and dense;
- every `λ ↦ E(λ)(g)` is holomorphic on `D`;
- every point has a connected open neighbourhood `W`, a scalar holomorphic `h₀` on `W` not
  identically zero, and holomorphic `h_g` on `W`, one for each `g`, with
  `h₀(λ) E(λ)(g) = h_g(λ)` on `D ∩ W`. The denominator `h₀` is the same for all `g ∈ G(𝔸)`.

This is BL's notion of meromorphy (§3.1) for functions with values in the space of all
functions on `G(𝔸)` with the topology of pointwise convergence. The continuation is required
to agree with `M(w, λ)φ` only on the regular region. That region is open and nonempty in the
real directions, so by the identity theorem the continuation is unique on `D` whenever it
exists (a mathematical remark; it is not used or proved here).

Provenance (derived). BL do not state this assertion separately. It is the form in which the
argument of §8.5 yields the continuation before the finite-dimensionality of the §8.2 Lemma is
used, and the following paragraph explains why. The constant term `C_{G,Q} E(φ, λ)` continues
meromorphically, since `E(φ, λ)` does (Theorem 2.3 (1)), with values in the space of smooth
functions of uniform moderate growth, on which point evaluations of constant terms are
continuous. `D(λ)` is a product of difference operators `ψ ↦ a·ψ − a^{ν(λ)} ψ` for a regular
`a ∈ A_Q`, with `ν(λ)` affine in `λ`. Let `T_a` be translation by `a` on `𝒜_Q(wμ_P)`. Then
`f(T_a) = 0`, and the restriction `D̃(λ)` of `D(λ)` to `𝒜_Q(wμ_P)` is `g(λ, T_a)`. Here
`f(x) = ∏_i (x − a^{w((μ_P)_i)})` comes from the exponents of `φ`, and `g(λ, x)` is the product
of the factors `x − a^{w'((μ_{P_{w'}})_i + λ) − wλ}` over `w' ≠ w`, as in BL. The
polynomials `f` and `g(λ, ·)` are coprime for generic `λ`. Their resultant `R(λ)` is a scalar
holomorphic function of `λ`, not identically zero. There are polynomials `u(x, λ)` and `v(x, λ)`
in `x`, with coefficients holomorphic in `λ`, such that `u f + v g = R`. Substituting `T_a`
gives `v(T_a, λ) D̃(λ) = R(λ)` on `𝒜_Q(wμ_P)`. So `R(λ) D̃(λ)⁻¹ = v(T_a, λ)` wherever
`R(λ) ≠ 0`. This is the journal's notation, p. 225; the arXiv TeX writes the resultant as
`R(λ, x)`. BL's formula therefore gives
`R(λ) M(w, λ)φ = v(T_a, λ)(D(λ)((C_{G,Q} E(φ, λ))_{-wλ}))` for generic `λ` in the region of
convergence. The right side applies a polynomial in the translation `T_a`, with holomorphic
coefficients, to a meromorphic family. Such a polynomial acts on all functions on `G(𝔸)` by
finitely many shifted evaluations. So `M(w, λ)φ` is a family that is meromorphic for the
topology of pointwise convergence, divided by the scalar holomorphic function `R(λ)`. Its
denominators are independent of the point `g`.

Conversely, the target, Theorem 2.3 (3), implies this statement mathematically: take
`E(λ) = ∑ coeff i λ • ψ i` and multiply the local denominators of the finitely many
coefficients. That direction is not formalized here.

## Reduction: `IntertwiningMeromorphicContinuationReductionStatement`

`IntertwiningFiniteSpanStatement.{u} → IntertwiningWeakMeromorphicContinuationStatement.{u} →
IntertwiningMeromorphicContinuationStatement.{u}`. It is proved by
`intertwiningMeromorphicContinuationReduction`.

Proof, as implemented.

1. Introduce all data and hypotheses of the target and apply both statements to them. This
   gives the following:
   - from the first statement, `ψ : Fin k → G(𝔸) → ℂ` in `𝒜_Q` and a threshold `R₁`;
   - from the second, `E`, `D` and a threshold `R₂`.
2. Put `R₀ = max R₁ R₂`. Regularity is monotone in the threshold (`isRegularParameter_mono`: if
   `R ≤ R'`, `R'`-regular implies `R`-regular). So for `R₀`-regular `λ` we have
   `E λ = M(w, λ)φ ∈ span (range ψ)`.
3. Apply `exists_meromorphic_expansion_of_mem_span` (module
   `Langlands.Analysis.Meromorphic.FiniteDimensionalValues`) with three inputs:
   - the property "automorphic on `V(𝔸)M'(F) \ G(𝔸)`";
   - the family `ψ` and the meromorphic `E`;
   - the set `S` of `R₀`-regular `λ`.

   It returns a linearly independent subfamily `ψ'` of `ψ`, which is still automorphic, and
   coefficients `coeff i λ = Φ(E λ) i`. Here `Φ` is a continuous linear left inverse of
   `c ↦ ∑ c_i ψ'_i`, built from finitely many point evaluations. The coefficients are
   meromorphic in linear coordinates with domain `D`, because they are images of `E` under
   continuous linear maps. They satisfy `E λ g = ∑ i, coeff i λ * ψ' i g` for `λ ∈ S`.
4. Rewrite `E λ` back to `M(w, λ)φ` on `S`. The witnesses of the target are
   `k := m`, `ψ := ψ'`, `coeff`, `D` and `R₀`.

The proof uses only the two statements, the generic lemmas of
`Langlands.Analysis.Meromorphic.FiniteDimensionalValues` and Mathlib. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Scope

- Neither `IntertwiningFiniteSpanStatement` nor
  `IntertwiningWeakMeromorphicContinuationStatement` is proved here. The target is therefore not
  proved by this module. Their proofs are the remaining obligations of Task 5501. They are
  expected to use these results: Harish-Chandra's finiteness theorem for the first; for the
  second, the continuation of Eisenstein series (`EisensteinMeromorphicContinuationStatement`),
  their constant terms (`EisensteinConstantTermStatement`) and the convergence of the
  intertwining integral (`IntertwiningAbsoluteConvergenceStatement`).
- The module claims nothing about holomorphy on the region of convergence, functional
  equations, the cocycle relation or the location of singularities.
