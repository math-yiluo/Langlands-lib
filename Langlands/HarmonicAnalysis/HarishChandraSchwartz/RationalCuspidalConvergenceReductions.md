# Reductions of the actual central and radical convergence targets

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceReductions`,
namespace `Langlands.HarishChandraSchwartz`. It imports `RationalCuspidalConvergenceStatements`
(the targets `RationalSchwartzCentralConvergenceStatement` and
`RationalSchwartzConstantTermConvergenceStatement`), `RationalConstantTerm`
(`RationalConstantTermEstimateStatement`, Proposition II.4.5 on actual points),
`RationalSquareIntegrableDecay` (`rationalTranslationWeights`) and
[XiCompactComparison](XiCompactComparison.md) (`rationalSchwartzSubmodule_eq`).

## Provenance

Internal. The module contains no new definitions or statements: it proves implications between
propositions already in the Library, so that the closed targets of
`RationalCuspidalConvergenceStatements` follow by applying the results below once their
hypotheses are proved. The mathematics is that of Waldspurger 2003 (VIII.4 for the central
projections `p_χ`, III.6 and Proposition II.4.5 for the convergence of constant terms; see the
Markdown of `RationalCentralProjection`, `ConstantTerm` and `RationalConstantTerm` for the source
correspondence); this module adds no source claim.

## Results

### Central convergence

- `RationalSplitCenterHeightStatement.schwartzCentralConvergence`:
  `RationalSplitCenterHeightStatement.{u} → RationalSchwartzCentralConvergenceStatement.{u}`.

  *Proof.* Given all data of the target (connected reductive `G`, maximal split torus `i`, generic
  `ν`, compact open `K` with `G(F) = P₀(F) K`, closed `ρ`, split component `s`, Haar measure
  `μ_A` on `A_G(F)` and a continuous unitary character `χ`), the published
  `RationalSplitCenterHeightStatement.centralWeights` turns the hypothesis into the actual
  `CentralWeights μ_A Ξ σ` for `Ξ = rationalXi hKc hPK` and `σ = rationalHeight ρ`. The published
  `CentralWeights.convergesOn` then gives `CentralIntegralConvergesOn` on every submodule of the
  Schwartz space, in particular on `⊤`, for the unitary `χ`. Its instance argument
  `Nonempty (CompactOpenSubgroup G(F))` is supplied by `K`.

### Radical integrability

The setting is that of `RationalWeights`: `F` a nonarchimedean local field, `G` a group scheme
over `Spec F` (affine morphism, locally of finite type), `G(F) = rationalPoints G`,
`P₀(F) = standardParabolicPoints i ν ∅`, `Ξ_K = rationalXi hKc hPK` and `σ = rationalHeight ρ`.

- `integrable_mul_mul_of_constantTermEstimate`: let `K`, `K'` be compact open subgroups of `G(F)`
  with `G(F) = P₀(F) K = P₀(F) K'`, `ρ` a matrix representation (indexed by a nonempty finite
  type), `M`, `U` subgroups of `G(F)`, `ν_U` a measure on `U`, `δ : M →* ℝ≥0ˣ` and
  `Ξ^M, σ^M : M → ℝ`. If `ConstantTermEstimate ν_U δ Ξ_{K'} σ Ξ^M σ^M` holds (the estimate of
  Proposition II.4.5 written with `K'`), then for every `f` in
  `schwartzSubmodule Ξ_K σ` and all `x, y ∈ G(F)`, the function `v ↦ f(x v y)` on `U` is
  `ν_U`-integrable.

  *Proof.* By `rationalSchwartzSubmodule_eq` the Schwartz spaces for `Ξ_K` and `Ξ_{K'}` coincide,
  so `f ∈ schwartzSubmodule Ξ_{K'} σ`. By `rationalTranslationWeights` and
  `TranslationWeights.translate_mem_schwartzSubmodule`, the translate
  `translate y x⁻¹ f : z ↦ f(x z y)` is again in this space. The published
  `ConstantTermEstimate.integrable_of_mem_schwartzSubmodule` at `m = 1` gives the integrability of
  `u ↦ (translate y x⁻¹ f)(1 · u) = f(x u y)`.

- `RationalConstantTermEstimateStatement.integrable_mul_mul`: assume
  `RationalConstantTermEstimateStatement.{u}`, `G` connected reductive, `i` a maximal split torus,
  `ν` generic, and `J ⊆ simpleRelativeRoots i ν`. Let `K0` be a compact open subgroup with
  `SimultaneousStandardBasisAt i ν K0`, `FiniteCartanCovering F i ν K0` and
  `StandardLeviCartanCovering F i ν J K0`, and let `K'` be a compact open subgroup with
  `G(F) = P₀(F) K'` and `M_J(F) = (P₀(F) ∩ M_J(F)) (K' ∩ M_J(F))` (`hM'`, stated with
  `subgroupOf (standardLeviPoints i ν J)`). Then for every compact open `K` with
  `G(F) = P₀(F) K`, every closed `ρ : MatrixRepresentation G (Fin N)`, every Haar measure `ν_U` on
  `U_J(F) = standardUnipotentPoints i ν J`, every `f ∈ schwartzSubmodule Ξ_K σ` and all
  `x, y ∈ G(F)`, the function `v ↦ f(x v y)` is `ν_U`-integrable on `U_J(F)`.

  *Proof.* `RationalConstantTermEstimateStatement.constantTermEstimate` applied with `K0` and
  `K'` gives `ConstantTermEstimate ν_U δ_{U_J} Ξ_{K'} σ Ξ^{M_J} σ|_{M_J}`; then apply the
  previous result.

## Scope and what remains for the targets

- The first result proves target 1 of `RationalCuspidalConvergenceStatements` from
  `RationalSplitCenterHeightStatement`; it does not prove that statement.
- The radical results do not prove `RationalSchwartzConstantTermConvergenceStatement`. That
  statement has no hypothesis supplying `K0` (with the three structural premises) or `K'` (with
  the Levi Iwasawa factorization); these must be produced for each `G`, `i`, `ν` and
  `J = rootSet i ν I`, and `RationalConstantTermEstimateStatement` must be proved. The subgroup
  `K` defining the Schwartz space is arbitrary in the results above; no Levi Iwasawa
  factorization is required of it.
- Properness of `J` is not used: the results hold for every `J ⊆ simpleRelativeRoots i ν`.
