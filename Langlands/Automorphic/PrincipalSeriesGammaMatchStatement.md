# Pair gamma comparison for principal-series constituents

Module `Langlands.Automorphic.PrincipalSeriesGammaMatchStatement` defines one proposition,
`Langlands.ClassField.Global.RelativeWeilGroup.PrincipalSeriesPairGammaMatchStatement`
(universes `u`, `uV`, `uE`). It is a statement only; nothing is proved here.

## Statement

Let `K` be a `p`-adic field, `eC` a common-closure reciprocity family, `ε` a common-closure
local-constant assignment with `hε : IsSystem K eC ε`, and `e` a rank-one reciprocity
candidate of `K` with `IsBaseReciprocity K e eC`. Let `ψ` be any nontrivial additive character
of `K`, and let `μ : Fin (r + 1) → QuasiCharacter K`, `μ' : Fin (t + 1) → QuasiCharacter K` be
arbitrary (not necessarily unramified or unitary) quasi-characters. Assume:

- `π` has a representative that is generic for `ψ` (`Whittaker.IsGeneric`, which includes
  irreducibility and admissibility) and is a subquotient (`IsSubquotientOf`) of the normalized
  principal series `principalSeries K r μ`, induced from the upper Borel subgroup;
  likewise `π'` with `μ'` and rank `t + 1`;
- `X` has a representative `B` with zero monodromy and continuous Weil action, and a basis
  `b` of `B` indexed by `Fin (r + 1)` together with a permutation `σ` such that every element
  `g` of the local Weil group acts by an upper triangular matrix in `b` whose `i`-th diagonal
  entry is `(μ (σ i) ∘ e)(g)` (`weilCharacter K e (μ (σ i)) g`); likewise `Y` with `μ'`, rank
  `t + 1` and a permutation `σ'`.

Then `IsPairGammaMatch K eC ε hε ψ π π' X Y`: a self-dual Haar measure for `ψ` exists, and for
each such measure one rational function is both `γ(s, π × π', ψ)` and the arithmetic
`γ(s, X ⊗ Y, ψ)` for the system `ε`.

The upper-triangular hypothesis says that `B` is a successive extension of the characters
`μ (σ i) ∘ e`; it covers non-semisimple representations as well as the direct sum
`⊕ μ_i ∘ e`.

## Provenance (derived)

- Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of Math. 123
  (1986), §2.7(iii) (printed p. 154, PDF p. 11): for `σ` a sum of characters and `π(σ)` the
  corresponding principal-series element, `L(σ ⊗ τ) = L(π(σ) × π(τ))` and
  `ε(σ ⊗ τ) = ε(π(σ) × π(τ))`; §2.8 (same page): the unramified irreducible subquotient of the
  induced representation is `π(σ)` for every ordering of the characters.
- Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
  (1983), Theorem 3.1 (multiplicativity of the gamma factor for induced representations of
  Whittaker type), which reduces `γ(s, π × π', ψ)` to `∏_(i,j) γ(s, μ_i μ'_j, ψ)`.

On the arithmetic side the gamma factor of `X ⊗ Y` is multiplicative in short exact sequences
of continuous Weil representations with zero monodromy (epsilon factors are additive and the
inertia invariants are exact), so it equals `∏_(i,j) γ(s, μ_i μ'_j ∘ e, ψ)`, and the rank-one
normalization of the system identifies these with Tate's factors through `e`.

The proposition is stated with the Library's vocabulary, for generic subquotients rather than
the canonical principal-series element `π(σ)`, and for upper-triangular rather than semisimple
parameters; hence it is recorded as derived content.

Design choices and why they are needed for truth:

- Continuity of `B`, `B'` is assumed because the arithmetic pair epsilon factor is only defined
  through continuous base restrictions; a non-continuous extension of continuous characters
  would have no arithmetic factor.
- Zero monodromy is assumed; with nonzero monodromy (for example the Steinberg parameter) the
  arithmetic L-factor differs from that of the semisimplification.
- Genericity of `π`, `π'` selects the constituent whose Rankin–Selberg factors are those of the
  induced representation.
- The permutations `σ`, `σ'` allow the diagonal of a triangularization to come in any order.

## Intended use

At unramified places of a weakly associated pair, the local components are generic spherical
constituents of unramified principal series and the arithmetic parameters are unramified, so
after a twist by an arbitrary global character this statement gives the local gamma equality
(the `OutsideGammaStability` input of the Library adapter
`Langlands.Global.FunctionalEquationComparison.relativeGammaComparison`, Henniart 2000 §2).
