# Root-hyperplane form of Eisenstein series, jointly in `(λ, g)`

Module `Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement`
states one proposition,
`Langlands.Global.EisensteinJointRootHyperplaneStatement`. It proves
nothing.

The proposition strengthens the published
`Langlands.Global.EisensteinRootHyperplaneStatement` (module
`Langlands.Global.AdelicRootHyperplaneStatement`). That statement gives,
for every `g` separately, some holomorphic `h` with
`h = (∏ β, B(· - λ₀, β))^m · EP(·) g`. The new statement asks for one
function `h(s, g)` that is jointly continuous, holomorphic in `s`, left
`G(F)`-invariant in `g` and built from nonzero root forms. Lapid's proof of
Proposition 6 (Lapid 2011, pp.329–330) needs these properties: it compares
the value of a wave packet at a point `x₀` with its values on a
neighbourhood of `x₀` in `G(F) \ G(𝔸)`, uniformly in `λ`. It is the
prerequisite of Task 5613
(`ccfc4843-fa56-468c-bf2f-811151ff64c8`, Lapid's Proposition 6) that the
contract of that task describes as "the local description of the
singularities along finitely many root hyperplanes, uniformly in `g`".

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3 (1), journal p.191 (PDF page 5): `E(φ, λ)` extends to a
  meromorphic function `λ ↦ E(φ, λ) ∈ 𝒜_umg(X)` on `𝔛_P`, and whenever it is
  regular, `E(φ, λ) ∈ 𝒜_G`. In particular `E(φ, λ)` is a function on
  `X = G(F) \ G(𝔸)`, that is, left `G(F)`-invariant.
- Theorem 2.3 (6), same page: the singularities of `E(φ, λ)` are along root
  hyperplanes.
- The Corollary at the end of §8.6, p.226 (PDF page 40; TeX source
  `1911.02342.tex`, lines 3537–3546): for any `λ₀ ∈ 𝔛_P` there are `R > 0`
  and an integer `k ≥ 0` such that
  `(∏_{β ∈ Φ_P} ⟨λ - λ₀, β^∨⟩^k) E(φ, λ)` admits a convergent power series
  expansion around `λ₀` in the Fréchet space `𝔉^R_smth(X)`.
- §7.1, p.211 (PDF page 25; TeX lines 1901–1908): `𝔉^R(X)` is the space of functions on
  `X` majorized by `e^{R‖H₀(·)‖}` on a Siegel domain, with the
  corresponding weighted sup norm, and `𝔉^R_smth(X)` is its smooth part.

Only the number field case is stated.

## Statement

The data and hypotheses are those of
`EisensteinRootHyperplaneStatement`: a number field `F`, a connected
reductive `G`, a parabolic `p : P → G` with geometric unipotent radical
`iU`, a rational Levi `l : M → P`, a presentation
`r : ParabolicRootPresentation p l a` through the split component
`a : A → M`, a maximal compact `K` with `hK : IsIwasawaCompact p K`, a
closed matrix embedding `rho`, and `φ` automorphic on
`U(𝔸) M(F) \ G(𝔸)`. It quantifies `EP : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and `DP`
such that `λ ↦ EP λ g` is meromorphic with domain `DP` for every `g`
(`IsMeromorphicInCoordinatesOn`), and, for some `R`,
`EP λ = hK.eisensteinSeries φ λ` whenever `r.IsRegularParameter hA hT R λ`.

The conclusion: for every linear coordinate system
`e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ` and every `s₀ ∈ ℂⁿ` there are

- a finite set `S ⊆ r.unipotentRoots` of roots of `A` in the unipotent
  radical, with `r.realRootFunctional hA hT β ≠ 0` for every `β ∈ S`,
- an exponent `m`, an open set `W ∋ s₀`,
- a function `h : ℂⁿ → G(𝔸) → ℂ`,

such that

1. `(s, g) ↦ h s g` is continuous on `W × G(𝔸)`;
2. `s ↦ h s g` is complex differentiable on `W` for every `g`;
3. `h s (c * g) = h s g` for `s ∈ W`, `c ∈ rationalSubgroup F G` (the
   image of `G(F)`) and every `g`;
4. for every `g` and every `s ∈ W` with `e s ∈ DP`,
   `h s g = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀))^m * EP (e s) g`.

The root forms `realRootFunctional` and `rootFunctional`
(`x ↦ B(x|_A, β)` and its complex-linear extension) are those of the
published module `Langlands.Global.AdelicRootHyperplaneStatement`.

## Correspondence with the source

- Root hyperplanes, the product form, the exponent and the roots: as in the
  Markdown of `EisensteinRootHyperplaneStatement`. BL's
  `⟨λ - λ₀, β^∨⟩` is a positive multiple of `B(λ - λ₀, β)`, BL's product
  runs over all of `Φ_P` with one exponent `k`, and the statement allows any
  finite subset of `r.unipotentRoots` with one exponent `m`.
- Nonzero root forms. For `β ∈ r.unipotentRoots`, `β ≠ 0`, the form `B` is
  positive definite, and restriction `X^*(P) ⊗ ℝ → X^*(A) ⊗ ℝ` is onto. So
  `x ↦ B(x|_A, β)` is not zero. The published Markdown of
  `AdelicRootHyperplaneStatement` (section Helpers) records this fact
  without proving it. The clause makes explicit that every factor of the
  product is a genuine hyperplane. Without it the product could vanish
  identically, and the conclusion would say nothing.
- Joint continuity and holomorphy. By BL's Corollary,
  `Φ(λ) = (∏ ⟨λ - λ₀, β^∨⟩^k) E(φ, λ)` is given near `λ₀` by a convergent
  power series in the Fréchet space `𝔉^R_smth(X)`. So `λ ↦ Φ(λ)` is
  continuous into `𝔉^R_smth(X)` and holomorphic. The weighted sup norm of
  `𝔉^R(X)` dominates the sup norm on every compact subset of `X`. Each
  `Φ(λ)` is smooth, in particular continuous. Hence
  `(λ, x) ↦ Φ(λ)(x)` is jointly continuous. Pulled back along
  `G(𝔸) → X` and the coordinates `e`, this is `h` on a small `W`, with `k`
  replaced by `m` and `Φ_P` by its subset `S` as in the published
  statement.
- Invariance. `Φ(λ)` is a function on `X = G(F) \ G(𝔸)` (Theorem 2.3 (1)).
  So `h s (c * g) = h s g` for `c ∈ G(F)`.
- Universal form. As in the published statement, the continuation data
  `(EP, DP)` are quantified. Admissible data agree with BL's continuation
  on the intersection of the domains: both agree with `E(φ, λ)` on the
  regular region, and the identity theorem applies to meromorphic
  functions with local denominators on the connected space `ℂⁿ`. Hence `h`,
  built from BL's continuation, satisfies clause 4 on a dense subset of
  `W ∩ e⁻¹ DP` and, by continuity of both sides on `W ∩ e⁻¹ DP`, on all of
  it. This is explanatory and not proved here.
- Parabolics and the compact subgroup: as in the published statement,
  `P` need not be standard and `K` need not be in good position. The
  reductions are explained in the Markdown of the convergence and
  continuation statements.

## Relation to the published statement

Clauses 2 and 4 of the conclusion, with `h · g` for each `g`, are the
conclusion of `EisensteinRootHyperplaneStatement`. So the new statement
implies the published one. This implication is not proved here.

## Provenance

Derived. The statement combines BL Theorem 2.3 (1), Theorem 2.3 (6) and the
Corollary of §8.6 in the local form of the published
`EisensteinRootHyperplaneStatement`. The three added clauses come from the
Fréchet formulation of the Corollary and from automorphy of `E(φ, λ)`.
Worker 5550 formulated it for Task 5613.

## Scope

Only Eisenstein series of one parabolic, in the number field case, are
covered. Holomorphy on the imaginary axis for square-integrable `φ`, BL's
footnote in §8.6 and Lapid's Proposition 6, is not stated here. It is the
target of Task 5613.
