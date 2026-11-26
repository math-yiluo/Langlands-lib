# Root-hyperplane singularities of Eisenstein series from their cuspidal tests

Module `Langlands.Global.AdelicEisensteinGoodPositionRootHyperplaneReduction`
defines two propositions and proves the second:

- `Langlands.Global.EisensteinGoodPositionRootHyperplaneContinuationStatement`;
- `Langlands.Global.EisensteinGoodPositionRootHyperplaneReductionStatement`, proved
  by `Langlands.Global.eisensteinGoodPositionRootHyperplaneReduction`.

## The good-position statement

`EisensteinGoodPositionRootHyperplaneContinuationStatement` has the binders,
hypotheses and conclusion of `EisensteinRootHyperplaneContinuationStatement`
(module `Langlands.Global.AdelicRootHyperplaneContinuationStatement`). It adds
the instance `LocallyOfFiniteType G.X.hom`, a standard parabolic family
`𝓕 : StandardParabolicFamily F G`, and two hypotheses on the maximal compact
subgroup `K`:

- `IsIwasawaCompact (𝓕.p ⟨∅, _⟩) K`: `P₀(𝔸) K = G(𝔸)` for the minimal standard
  parabolic `P₀` of `𝓕`;
- for every standard index `J`, the inverse image of `K` in `M_J(𝔸)` is a
  maximal compact subgroup of `M_J(𝔸)`.

These are the conditions of Bernstein–Lapid, *On the meromorphic continuation
of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.1, p.190 (registered
as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`), on a maximal
compact subgroup in good position. The conclusion asks for one pointwise
meromorphic continuation `EP` of `E(φ, λ)`, with one domain `DP`, equal to the
series for `Re λ` sufficiently regular. Near every point `λ₀ = e s₀` it asks for
a finite set `S` of roots of `A` in the unipotent radical, an exponent `m` and an
open `W ∋ s₀` such that, for every `g`, the function
`(∏ β ∈ S, B(λ - λ₀, β))^m · EP(λ)(g)` agrees on `W` (where `e s ∈ DP`) with a
function holomorphic on `W`.

## The reduction

`EisensteinGoodPositionRootHyperplaneReductionStatement` is the implication

`EisensteinMeromorphicContinuationStatement → LeadingCuspidalInjectivityStatement →
LeviCuspFormPairingMajorantStatement → EisensteinCuspidalTestRootHyperplaneStatement →
EisensteinGoodPositionRootHyperplaneContinuationStatement`

(all in universe `u`). The premises are:

- `EisensteinMeromorphicContinuationStatement` (module
  `Langlands.Global.AdelicEisensteinContinuationStatement`): a continuation
  `E'` of `E(φ, λ)` with local meromorphic presentations `f` in the Fréchet
  spaces of uniform moderate growth `𝔉^R_L`, whose values are automorphic
  forms on `G(F) \ G(𝔸)` on the domains of the presentations;
- `LeadingCuspidalInjectivityStatement` (module
  `Langlands.Global.AdelicLeadingCuspidalInjectivityStatement`, BL Theorem 6.3);
- `LeviCuspFormPairingMajorantStatement` (module
  `Langlands.Global.AdelicLeviCuspFormMajorantStatement`): weighted majorants of
  cusp forms on standard Levi subgroups;
- `EisensteinCuspidalTestRootHyperplaneStatement` (module
  `Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneStatement`): the
  norm-one Levi pairings of the standard constant terms of `E(φ, λ)` with cusp
  forms have meromorphic continuations `Γ J ψ g`, and near each point one
  product of root forms clears all of them.

## Proof

The two lemmas in the namespace `Langlands.Global.StandardParabolicFamily` treat
one cuspidal test `v ↦ (C_J v(· g), ψ)` of a local presentation `f : W → 𝔉^R_L`
with domain `D`, given a family `E` of adelic functions with `f t = E t` on `D`.

- `hasLocalMeromorphicData_leviPairing_constantTerm`: the scalar function
  `t ↦ (C_J E(t)(· g), ψ)` has local meromorphic data
  (`HasLocalMeromorphicData`) at every point of `W`. This is
  `hasLocalMeromorphicData_of_isMeromorphicOn` applied to the continuous linear
  form `constantTermLeviPairingCLM`.
- `differentiableOn_leviPairing_constantTerm`: that function is complex
  differentiable on the image of `D`. This follows from the weak holomorphy of
  `f` on `D`, through `differentiableOn_extendOpens`.

The proof of `eisensteinGoodPositionRootHyperplaneReduction` runs as follows.

1. Choose one linear coordinate system `e₀ : ℂᵐ ≃ X^*(P) ⊗ ℂ`
   (`exists_complexParameterEquiv`) and a closed matrix embedding `rho'` of
   positive size with the same automorphic functions
   (`exists_positiveMatrixEmbedding_of_isClosedSubgroup`).
2. Apply the four premises with `rho'` to get:
   - the continuation `E'`, with agreement bound `R₀` and local presentations;
   - the continuations `Γ J ψ g` of the cuspidal tests, with their clearing data;
   - the majorants for every exponent.
   `positiveChamberNonempty` gives a `0`-regular parameter.
3. Point evaluations. The continuous evaluations
   `UniformGrowthFrechetSpace.evaluation` give local meromorphic data for
   `t ↦ E'(e₀ t)(g)` at every point.
4. Cuspidal clearing of a presentation. Fix `s₀` and the presentation
   `(W, R, L, f, D)` of `E'` at `s₀`. Take the root set `S`, the exponent `k` and
   the neighbourhood `W_c` given at `s₀` by the cuspidal-test premise. For a
   standard `J`, a cusp form `ψ` and `g ∈ G(𝔸)`, let
   `τ(t) = (C_J E'(e₀ t)(· g), ψ)`.
   - The first lemma at every point, and the gluing theorem
     `exists_isMeromorphicOn_of_local`, make `τ` meromorphic on `ℂᵐ` with some
     domain `D_τ`.
   - On the image of a nonempty open set of regular parameters
     (`exists_isOpen_isRegularParameter`), `τ` agrees with `Γ J ψ g ∘ e₀`,
     because both equal the pairing of the convergent series there.
   - The transfer lemma `exists_eq_mul_of_eqOn_isOpen` (module
     `Langlands.Global.AdelicRootHyperplaneReduction`) moves the clearing of
     `Γ J ψ g` to `τ`. It gives `h'`, holomorphic on `W_c`, with
     `h' = (∏ β ∈ S, B(e₀ t - e₀ s₀, β))^k · τ` on `W_c ∩ D_τ`.
   - The second lemma makes `τ` continuous on the image of `D`. The set `D_τ` is
     open and dense, so the identity extends to `W_c ∩ D`. There `τ` is the
     cuspidal test of `f`.

   This is `HasLocalCuspidalRootClearing` for the presentation, with one `S`,
   `k` and `W_c` for all tests.
5. Pole transfer. `hasLocalRootClearing_of_cuspidal_pairings` (module
   `Langlands.Global.AdelicLocalRootClearing`) uses the injectivity of leading
   cuspidal components, the good-position hypotheses and the majorants. It
   turns the cuspidal clearing into `HasLocalRootClearing` for all point
   evaluations of `E'` at `s₀`.
6. Coordinates. `exists_meromorphicInCoordinatesOn_of_local_rootClearing` (module
   `Langlands.Analysis.Meromorphic.CoordinateRootClearing`) turns the local data
   of steps 3 and 5 into one domain `DP` with pointwise meromorphy in linear
   coordinates, and into the local clearing in every linear coordinate system.
   Agreement with `E(φ, λ)` for `R₀`-regular `λ` is part of the continuation
   premise.

## Provenance

This is the pole-detection argument of BL §8.6, pp.225–226: "the singularities
of `E(φ, λ)` are precisely those of its cuspidal components" (Mœglin–Waldspurger
I.4.10). Detection by cuspidal components is implemented by the Library's pole
transfer through the norm-one Levi pairings (BL §6.2, (6.8)) and the injectivity
of Theorem 6.3. The location of the singularities of the cuspidal components is
the premise `EisensteinCuspidalTestRootHyperplaneStatement`. The good-position
case is separated from the general case. The module
`Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction` removes the
good-position hypotheses.
