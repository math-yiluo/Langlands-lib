# Root-hyperplane continuation of intertwining operators from a root factorization

Module `Langlands.Global.AdelicIntertwiningRootFactorizationReduction`. Its target is the
Library's `Langlands.Global.IntertwiningRootHyperplaneContinuationStatement` (module
`Langlands.Global.AdelicRootHyperplaneContinuationStatement`), Bernstein–Lapid, Theorem 2.3 (3)
and (6), number field case.

The module states one result, `Langlands.Global.IntertwiningRootFactorizationStatement`, and
proves that it implies the target:

- `Langlands.Global.IntertwiningRootFactorizationReductionStatement` is the implication
  `IntertwiningRootFactorizationStatement.{u} → IntertwiningRootHyperplaneContinuationStatement.{u}`;
- `Langlands.Global.intertwiningRootFactorizationReduction` proves it.

The module does not prove `IntertwiningRootFactorizationStatement`, so it does not prove the
target.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Locators are journal pages of the
PDF in that folder, with the TeX file `1911.02342.tex` for line numbers.

- Theorem 2.3 (3) and (6), p. 191 (TeX lines 458–469): `λ ↦ M(w, λ)φ`, with values in a
  finite-dimensional subspace of `𝒜_Q`, admits a meromorphic continuation, and its
  singularities are along root hyperplanes.
- §8.6, p. 225 (TeX lines 3517–3523): "If `w` is an elementary symmetry `s_α` for some
  `α ∈ Δ_P`, then as a function of `λ ∈ 𝔛_P`, `M(w, λ)` depends only on `⟨λ, α^∨⟩`. In
  general, by decomposing `w` into elementary symmetries [Mœglin–Waldspurger I.1.8] and using
  the multiplicativity of intertwining operators (cf. [Mœglin–Waldspurger II.1.6]), it follows
  that the singularities of `M(w, λ)` are of the form `⟨λ, β^∨⟩ = c` for some `β ∈ Φ_P` such
  that `wβ < 0` and `c ∈ ℂ`."
- The Corollary at the end of §8.6, p. 226, for the local form of the conclusion (a power of
  `∏_β ⟨λ - λ₀, β^∨⟩` clears the singularities near `λ₀`).

## Statement: `IntertwiningRootFactorizationStatement`

It has exactly the binders and hypotheses of `IntertwiningRootHyperplaneContinuationStatement`,
in the same order: the parabolics `P = MU` (presentation `r`) and `Q = M'V`, `(w, c)` presenting
an element of `W(P, Q)`, the retraction `π'` with `l' ≫ π' = 𝟙 M'`, a maximal compact `K`
with `P(𝔸)K = Q(𝔸)K = G(𝔸)`, a closed matrix embedding `rho` and `φ ∈ 𝒜_P`. It asserts that
there are

- `k`, functions `ψ : Fin k → (G(𝔸) → ℂ)`, scalar functions
  `coeff : Fin k → (X^*(P) ⊗ ℂ → ℂ)` and a set `D`, with every `coeff i` meromorphic with
  domain `D` in linear coordinates (`IsMeromorphicInCoordinatesOn`);
- a bound `R` such that
  `hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g` for all `g`
  whenever `r.IsRegularParameter hA hT R λ`;
- natural numbers `J` and `n` and factors
  `fac : Fin k → Fin J → Fin n → (X^*(P) ⊗ ℂ → ℂ)` such that
  `coeff i x = ∑ j, ∏ t, fac i j t x` for every `i` and every `x ∈ D`, and each factor
  `fac i j t` is of one of two kinds:
  - holomorphic everywhere: `fac i j t ∘ e` is complex differentiable on `ℂᵐ` for every
    linear coordinate system `e : ℂᵐ ≃ X^*(P) ⊗ ℂ`;
  - a function of one root form: `fac i j t` is meromorphic with domain `D` in linear
    coordinates, and there is `β ∈ r.unipotentRoots` such that
    `fac i j t (x + ν) = fac i j t x` whenever `x ∈ D`, `x + ν ∈ D` and
    `r.rootFunctional hA hT β ν = 0`.

Here `r.rootFunctional hA hT β` is the complex linear form `λ ↦ B(λ|_A, β)` of the module
`Langlands.Global.AdelicRootHyperplaneStatement`, and `r.unipotentRoots` is the set of nonzero
restrictions to `A` of the positive relative roots.

The first two items are word for word the first two conjuncts of
`IntertwiningRootHyperplaneContinuationStatement`; the third replaces its last conjunct (the
local root-product form) by the factorization.

## Correspondence with the source (provenance: derived)

Bernstein–Lapid do not state this factorization separately. It records what the argument of
§8.6 quoted above produces, before the singularities are read off:

- For an elementary symmetry `s_α`, the operator `M(s_α, λ)` depends on `λ` only through
  `⟨λ, α^∨⟩`. On finite-dimensional spaces of automorphic forms containing the values (Theorem
  2.3 (3)), its matrix coefficients are therefore meromorphic functions invariant under
  translation by the kernel of `λ ↦ ⟨λ, α^∨⟩`.
- Writing `w = s_{α_r} ⋯ s_{α_1}` with elementary symmetries and `w_t = s_{α_t} ⋯ s_{α_1}`,
  multiplicativity gives `M(w, λ) = M(s_{α_r}, w_{r-1}λ) ∘ ⋯ ∘ M(s_{α_1}, λ)`. The coefficient
  of `M(w, λ)φ` along a basis vector is a sum, over the paths through the chosen bases, of
  products of matrix coefficients of the factors. The `t`-th factor depends on `λ` only
  through `⟨w_{t-1}λ, α_t^∨⟩ = ⟨λ, β_t^∨⟩` with `β_t = w_{t-1}⁻¹ α_t ∈ Φ_P`.
- The Library's root forms are `λ ↦ B(λ|_A, β)` for the Weyl-induced positive form `B`. The
  coroot form `λ ↦ ⟨λ, β^∨⟩` on `X^*(P) ⊗ ℂ` is a nonzero multiple of it, so the two have the
  same kernel; the invariance in the statement is stated with `r.rootFunctional`.
- The factors holomorphic everywhere absorb entire normalizing factors, such as the factor
  `exp⟨(γw)λ, H_{γQγ⁻¹}(γ)⟩` that relates `M(w, λ)φ` for a non-standard `Q` to the operator for
  the standard conjugate `γQγ⁻¹` (see the Markdown of
  `Langlands.Global.IntertwiningMeromorphicContinuationStatement`).
- Sums over `j` and products over `t` have fixed lengths `J` and `n`; shorter sums and products
  are padded with the constant factors `0` and `1`, which are holomorphic everywhere.
- The factors are given with the same domain `D` as the coefficients. Finitely many open
  dense domains intersect in an open dense domain, on which every factor and coefficient is
  still meromorphic.

These points are explanatory: neither the factorization nor the proportionality of the forms
is proved in this module.

## Reduction: `intertwiningRootFactorizationReduction`

Proof, as implemented.

1. Introduce the premise and all data and hypotheses of the target, and apply the premise to
   them. This gives `k`, `ψ`, `coeff`, `D`, the meromorphy of the coefficients, the agreement
   on the regular region, and `J`, `n`, `fac` with the two properties above.
2. The witnesses of the target are `k`, `ψ`, `coeff` and `D`; its first two conjuncts are the
   corresponding conclusions of the premise.
3. Every factor has poles along the root hyperplanes, in the sense of
   `Langlands.Analysis.Meromorphic.HasRootHyperplanePoles` for the forms
   `r.rootFunctional hA hT` and the allowed set `r.unipotentRoots` (module
   `Langlands.Analysis.Meromorphic.RootHyperplanePoles`):
   - a factor holomorphic everywhere has none (`hasRootHyperplanePoles_of_differentiable`);
   - an invariant factor has them along the single form of its root `β`, by the one-variable
     criterion `hasRootHyperplanePoles_of_kernel_invariant`.
4. The predicate is stable under finite products and sums
   (`HasRootHyperplanePoles.finset_prod`, `HasRootHyperplanePoles.finset_sum`), so
   `x ↦ ∑ j, ∏ t, fac i j t x` has poles along the root hyperplanes. Since it agrees with
   `coeff i` on `D`, so does `coeff i` (`HasRootHyperplanePoles.congr`).
5. For the last conjunct of the target, fix a coordinate system `e` and a centre `s₀`.
   `exists_rootPoleData_sum_mul` chooses one finite set `S ⊆ r.unipotentRoots`, one exponent
   and one open neighbourhood of `s₀` for all coefficients at once, before the point `g`, and
   then gives for each `g` a function complex differentiable on that neighbourhood that equals
   `(∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m * ∑ i, coeff i (e s) * ψ i g` wherever
   `e s ∈ D`. Its conclusion is literally the last conjunct of the target.

The proof uses only the premise, the module `Langlands.Analysis.Meromorphic.RootHyperplanePoles`
and Mathlib. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Scope

- `IntertwiningRootFactorizationStatement` is not proved here. Its proof needs the meromorphic
  continuation of intertwining operators (`IntertwiningMeromorphicContinuationStatement`),
  the dependence of the operator of an elementary symmetry on one coroot coordinate, the
  decomposition of `w` into elementary symmetries and the multiplicativity of the continued
  operators (`IntertwiningCocycleStatement`), and the proportionality of the coroot forms to
  the Library's root forms.
- No claim is made that only roots `β` with `wβ < 0` occur; the statement allows every root of
  `r.unipotentRoots`, as the target does.
