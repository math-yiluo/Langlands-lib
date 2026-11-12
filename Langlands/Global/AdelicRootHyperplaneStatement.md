# Singularities along root hyperplanes

Module `Langlands.Global.AdelicRootHyperplaneStatement` defines two linear
forms on parameter spaces and states three propositions:
`Langlands.Global.IntertwiningRootHyperplaneStatement`,
`Langlands.Global.EisensteinRootHyperplaneStatement` and their conjunction
`Langlands.Global.RootHyperplaneSingularitiesStatement`. Its only lemma is
the formula `ParabolicRootPresentation.rootFunctional_tmul`. It proves none
of the statements.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3 (6), journal p.191 (PDF page 5): the singularities of
  `M(w, λ)φ` are along root hyperplanes; the same is true for the
  singularities of `E(φ, λ)`.
- §8.6, journal pp.225–226 (PDF pages 39–40), proof of (6): the
  singularities of `M(w, λ)` are of the form `⟨λ, β^∨⟩ = c` for some
  `β ∈ Φ_P` with `wβ < 0` and `c ∈ ℂ`; those of `E(φ, λ)` are those of its
  cuspidal components, hence also along root hyperplanes.
- The Corollary at the end of §8.6, p.226 (PDF page 40): for any `λ₀ ∈ 𝔛_P`
  there are `R > 0` and an integer `k ≥ 0` such that
  `(∏_{β ∈ Φ_P} ⟨λ - λ₀, β^∨⟩^k) E(φ, λ)` has a convergent power series
  expansion around `λ₀` in the Fréchet space `𝔉^R_smth(X)`.

Only the number field case is stated.

## Helpers

Let `r : ParabolicRootPresentation p l a` present the parabolic `P = MU`
with split component `a : A → M`, and let `β` be a character of `A`.

- `r.realRootFunctional hA hT β : X^*(P) ⊗ ℝ → ℝ` is
  `x ↦ B(x|_A, β)`, where `B` is the published positive definite form
  `Langlands.Plancherel.weylInducedCharacterForm hA hT f i` on
  `X^*(A) ⊗ ℝ` and `x|_A` is `realParameterRestriction (a ≫ l) x`. These
  are the form and the restriction of
  `ParabolicRootPresentation.IsRegularParameter`
  (module `Langlands.Global.AdelicEisensteinConvergenceStatement`), which
  reads `R < r.realRootFunctional hA hT α (Re λ)` for all `α` in
  `r.unipotentRoots`.
- `r.rootFunctional hA hT β : X^*(P) ⊗ ℂ → ℂ` is its complex-linear
  extension: `s ⊗ χ ↦ s · B((1 ⊗ χ)|_A, β)` (lemma `rootFunctional_tmul`).

For `β` a root of `A` in the unipotent radical (`β ∈ r.unipotentRoots`) the
zero set of `rootFunctional β` is BL's root hyperplane `⟨λ, β^∨⟩ = 0`, and
`{λ | rootFunctional β (λ - λ₀) = 0}` is the root hyperplane through `λ₀`.
Indeed, as explained in the Markdown of the convergence statement, for a
relative root `β₀` of the maximal split torus `T` restricting to `β`,
`⟨x, β₀^∨⟩ = 2 B_T(x, β₀) / B_T(β₀, β₀)` for the relative-Weyl-invariant form
`B_T`, and for `x` a parameter of `P` this is a positive multiple of
`B(x|_A, β)`. Both sides are linear in `λ`, so the complex forms are
proportional as well. The form `rootFunctional β` is not zero: `β ≠ 0`, `B`
is positive definite and restriction `X^*(P) ⊗ ℝ → X^*(A) ⊗ ℝ` is onto (the
characters of `M` restricted to its split component `A` span
`X^*(A) ⊗ ℚ`). These facts are explanatory and not proved here.

## Statements

`IntertwiningRootHyperplaneStatement` has the data and hypotheses of
`Langlands.Global.IntertwiningMeromorphicContinuationStatement` (staged with
this program; parabolics `P = MU` with presentation `r` and `Q = M'V`,
`(w, c)` presenting an element of `W(P, Q)`, `π' : Q → M'` with
`l' ≫ π' = 𝟙 M'`, a maximal compact `K` with `P(𝔸)K = Q(𝔸)K = G(𝔸)`, a closed
matrix embedding `rho` and `φ ∈ 𝒜_P`). It quantifies continuation data
`k`, `ψ : Fin k → (G(𝔸) → ℂ)`, `coeff : Fin k → (X^*(P) ⊗ ℂ → ℂ)` and `D`
with every `coeff i` meromorphic with domain `D`
(`IsMeromorphicInCoordinatesOn`, module
`Langlands.Analysis.Meromorphic.LinearCoordinates`) and, for some `R`,
`hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g`
for all `g` whenever `r.IsRegularParameter hA hT R λ`. The conclusion: for
every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every `s₀ ∈ ℂⁿ`
there are a finite set `S` of roots of `A` in the unipotent radical
(`S ⊆ r.unipotentRoots`), an exponent `m` and an open `W ∋ s₀` such that for
every `g ∈ G(𝔸)` some `h : ℂⁿ → ℂ`, complex differentiable on `W`, satisfies

`h s = (∏ β ∈ S, rootFunctional β (e s - e s₀))^m * ∑ i, coeff i (e s) * ψ i g`

for all `s ∈ W` with `e s ∈ D`.

`EisensteinRootHyperplaneStatement` has the data and hypotheses of
`Langlands.Global.EisensteinAbsoluteConvergenceStatement`. It quantifies
`EP : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and `DP` such that for every `g` the function
`λ ↦ EP λ g` is meromorphic with domain `DP`, and for some `R`,
`EP λ = hK.eisensteinSeries φ λ` whenever `λ` is `R`-regular. The conclusion
is the same with `EP (e s) g` in place of the sum and `DP` in place of `D`.

`RootHyperplaneSingularitiesStatement` is the conjunction of the two.

## Correspondence with the source

- Local form. Near `λ₀`, "the singular set lies in root hyperplanes" is
  equivalent to the local product form above. If the polar set of a
  meromorphic germ `f` at `λ₀` lies in a union of hyperplanes through `λ₀`,
  write `f = h/g` with `h`, `g` coprime in the factorial ring of germs of
  holomorphic functions at `λ₀`. The polar set is the zero set of `g`, so
  each irreducible factor of `g` vanishes exactly on one of the hyperplanes
  and is a unit times its linear form. Hence a power of the product of the
  linear forms is divisible by `g`. Conversely the product form shows that
  the singularities near `λ₀` lie in the hyperplanes of `S`. Polar sets of
  meromorphic functions on `ℂⁿ` are locally finite unions of irreducible
  hypersurfaces. So near `λ₀` only the hyperplanes through `λ₀` matter,
  after shrinking `W`. This is the form of BL's Corollary in §8.6, with
  `S ⊆ Φ_P` and `k = m`.
- Uniformity in `g`. One `S`, `m` and `W` serve all `g`. For `M(w, λ)φ` this
  holds because its values lie in a finite-dimensional space: take a basis
  and the maximum of the exponents of its coefficients. For `E(φ, λ)` it is
  BL's Corollary: a power series in the Fréchet space `𝔉^R_smth(X)` gives a
  convergent scalar power series at each `g`.
- Roots. BL use `β ∈ Φ_P` with `wβ < 0` for `M(w, λ)`. The statement allows
  every root of `A` in the unipotent radical of `P`. This is weaker than BL's
  proof gives and is what Theorem 2.3 (6) asserts.
- Universal form. As in the functional equation and cocycle statements, the
  continuation data are quantified. Any admissible data agree with BL's
  continuation on the intersection of the domains (identity theorem; see the
  Markdown of the functional equation statement). Hence `h`, built from
  BL's continuation, agrees with the product times the given data on a
  dense open subset of `W ∩ D`, and by continuity on all of `W ∩ D`. This is
  explanatory and not proved here.
- Holomorphy of `h` is complex differentiability on the open set `W ⊆ ℂⁿ`
  (Mathlib's `DifferentiableOn ℂ`).
- Parabolics and the compact subgroup: as in the continuation statements,
  `Q` need not be standard and `K` need not be in good position; the
  reductions are explained in the Markdown of the convergence and
  continuation statements.

## Scope

The existence of the continuations (BL 2.3 (1), (3)) is stated separately.
The refinement `wβ < 0`, holomorphy on the imaginary axis for square
integrable `φ` (BL footnote in §8.6) and the function field case are not
stated.
