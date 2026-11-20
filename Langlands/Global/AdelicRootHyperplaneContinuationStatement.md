# Continuations with singularities along root hyperplanes

Module `Langlands.Global.AdelicRootHyperplaneContinuationStatement` states
three propositions and proves none of them:
`Langlands.Global.IntertwiningRootHyperplaneContinuationStatement`,
`Langlands.Global.EisensteinRootHyperplaneContinuationStatement` and their
conjunction `Langlands.Global.RootHyperplaneContinuationStatement`.

They are the existential counterparts of the two halves of
`Langlands.Global.RootHyperplaneSingularitiesStatement` (module
`Langlands.Global.AdelicRootHyperplaneStatement`, Bernstein–Lapid
Theorem 2.3 (6)). That statement takes any continuation data and asserts the
root-hyperplane form for them. These statements assert that some
continuation data exist and have the root-hyperplane form.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3, journal p.191 (PDF page 5): (1) `E(φ, λ)` admits a
  meromorphic continuation to `𝔛_P`; (3) `M(w, λ)` admits a meromorphic
  continuation to `𝔛_P`; (6) the singularities of `M(w, λ)φ`, and those of
  `E(φ, λ)`, are along root hyperplanes.
- §8.6, journal pp.225–226 (PDF pages 39–40), proof of (6), and the
  Corollary at its end: for any `λ₀ ∈ 𝔛_P` there are `R > 0` and `k ≥ 0` such
  that `(∏_{β ∈ Φ_P} ⟨λ - λ₀, β^∨⟩^k) E(φ, λ)` has a convergent power series
  expansion around `λ₀` in the Fréchet space `𝔉^R_smth(X)`.

Only the number field case is stated.

## Statements

`IntertwiningRootHyperplaneContinuationStatement` has exactly the binders
and hypotheses of `IntertwiningRootHyperplaneStatement`, in the same order, up
to and including the automorphy of `φ`. These are the parabolics `P = MU`
(presentation `r`) and `Q = M'V`, `(w, c)` presenting an element of
`W(P, Q)`, `π' : Q → M'` with `l' ≫ π' = 𝟙 M'`, a maximal compact `K` with
`P(𝔸)K = Q(𝔸)K = G(𝔸)`, a closed matrix embedding `rho` and `φ ∈ 𝒜_P`. It
then asserts that there are

- `k`, functions `ψ : Fin k → (G(𝔸) → ℂ)`, scalar functions
  `coeff : Fin k → (X^*(P) ⊗ ℂ → ℂ)` and a set `D`, with every `coeff i`
  meromorphic with domain `D` in linear coordinates
  (`IsMeromorphicInCoordinatesOn`);
- a bound `R` such that
  `hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g`
  for all `g` whenever `r.IsRegularParameter hA hT R λ`;
- for this choice, the conclusion of `IntertwiningRootHyperplaneStatement`:
  for every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every
  `s₀ ∈ ℂⁿ` there are a finite set `S ⊆ r.unipotentRoots`, an exponent `m`
  and an open `W ∋ s₀` such that for every `g` some `h`, complex
  differentiable on `W`, satisfies
  `h s = (∏ β ∈ S, rootFunctional β (e s - e s₀))^m * ∑ i, coeff i (e s) * ψ i g`
  for all `s ∈ W` with `e s ∈ D`.

The first two items are the data and hypotheses that
`IntertwiningRootHyperplaneStatement` quantifies universally. They are also
the conclusion of `Langlands.Global.IntertwiningMeromorphicContinuationStatement`
(module `Langlands.Global.AdelicIntertwiningContinuationStatement`), without
its clause that every `ψ i` is an automorphic form on `V(𝔸)M'(F) \ G(𝔸)`.

`EisensteinRootHyperplaneContinuationStatement` has exactly the binders and
hypotheses of `EisensteinRootHyperplaneStatement` up to the automorphy of
`φ`. It asserts that there are `EP : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and `DP` such
that

- for every `g` the scalar function `λ ↦ EP λ g` is meromorphic with domain
  `DP` in linear coordinates;
- for some `R`, `EP λ = hK.eisensteinSeries φ λ` whenever `λ` is `R`-regular;
- for this choice, the conclusion of `EisensteinRootHyperplaneStatement`: the
  same local product form with `EP (e s) g` in place of the sum and `DP` in
  place of `D`.

`RootHyperplaneContinuationStatement` is the conjunction of the two.

## Correspondence with the source

- Existence. BL 2.3 (1) and (3) give one continuation of `E(φ, λ)` and of
  `M(w, λ)φ`. BL 2.3 (6) and §8.6 say that its singularities lie along root
  hyperplanes. These statements assert exactly that some continuation has
  this property. The local product form, the uniformity of `S`, `m` and `W`
  in `g`, the roots allowed (all of `Φ_P`, not only those with `wβ < 0`) and
  holomorphy as complex differentiability are as in
  `RootHyperplaneSingularitiesStatement`; its Markdown explains why the local
  product form is equivalent to "the singular set lies in root hyperplanes".
- For `M(w, λ)φ` the continuation is a finite combination
  `∑ i, coeff i λ * ψ i`, as in the intertwining continuation statement. This
  works because in BL 2.3 (3) the map `λ ↦ M(w, λ)φ` takes values in a
  finite-dimensional subspace of `𝒜_Q`; the `ψ i` span it and the
  `coeff i` are the coefficients (see the Markdown of
  `IntertwiningMeromorphicContinuationStatement`). Automorphy of the `ψ i` is
  not required here.
- For `E(φ, λ)` the meromorphy is asked pointwise in `g` with one domain `DP`,
  as in the hypothesis of `EisensteinRootHyperplaneStatement`. It follows from
  the Fréchet continuation in `EisensteinMeromorphicContinuationStatement`:
  evaluation at `g` is a continuous linear functional. The domain can be
  taken as the complement of the root hyperplanes along which `E(φ, λ)` is
  singular (a locally finite union, BL §8.6).

## Relation to the universal statements

`RootHyperplaneContinuationStatement` differs from the target statement in
one respect: it asserts the root form for one continuation, whose existence
it also asserts, instead of for all admissible continuation data. The reduction in
`Langlands.Global.AdelicRootHyperplaneReduction` recovers the universal form
from it. Two admissible continuations agree on a nonempty open set of
regular parameters. That set exists by
`Langlands.Global.PositiveChamberNonemptyStatement`. By the identity theorem
for meromorphic functions the continuations agree wherever both are
holomorphic, so the product form transfers.
