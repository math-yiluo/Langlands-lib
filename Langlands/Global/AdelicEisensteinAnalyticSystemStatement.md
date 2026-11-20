# The analytic system characterizing Eisenstein series

Module `Langlands.Global.AdelicEisensteinAnalyticSystemStatement` states
`Langlands.Global.EisensteinAnalyticSystemStatement` as a proposition
definition. It supplies no proof.

The statement is the input that the principle of meromorphic continuation
(Bernstein–Lapid, Theorem 3.3; `MeromorphicContinuationHolomorphicStatement`
in `Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement`) needs in
order to give the meromorphic continuation of Eisenstein series
(`EisensteinMeromorphicContinuationStatement` in
`Langlands.Global.AdelicEisensteinContinuationStatement`).

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Locators refer to
the PDF `Bernstein-Lapid--On the meromorphic continuation of Eisenstein
series--2024.pdf` in that folder (journal page = PDF page + 186):

- §8.4, the system `Ξ_fnl(λ)` and its Proposition, journal pp.223–224 (PDF
  pp.37–38). The system `Ξ_fnl(λ)`, `λ ∈ 𝔛_P`, of linear equations on
  `ψ ∈ 𝔉_umg(X)` is holomorphic and locally of finite type. In the region
  `⟨Re λ, α^∨⟩ ≫ 0` for all `α ∈ Δ_P` its unique solution is `E(φ, λ)`. The
  second paragraph of the proof ("Conversely, suppose that
  `ψ ∈ Sol(Ξ_fnl(λ))` for some `λ ∈ 𝔛_P`") shows, through Lemma 8.1, that
  every solution at every parameter is an automorphic form.
- §8.1, Lemma ("Characterization of automorphic forms", Lemma 8.1), journal
  pp.221–222 (PDF pp.35–36). This is the criterion used in that step.
- §8.6, the Corollary at its end, journal p.226 (PDF p.40). For every bounded
  open `U ⊆ 𝔛_P` there is `R` such that `λ ↦ E(φ, λ)` is meromorphic on `U`
  with values in the Fréchet space `𝔉^R_smth(X)`. The authors say that
  "the proof shows" this. It is the proof of §8.4 with the system restricted
  to one Fréchet space `𝔉^R` over the bounded set `U`.
- §3.3, analytic systems of linear equations, journal pp.193–194 (PDF
  pp.7–8). Definitions (1) and (2) define a holomorphic system and a system
  locally of finite type.

## Setting

The hypotheses are those of `EisensteinMeromorphicContinuationStatement`, and
so of `EisensteinAbsoluteConvergenceStatement`:

- a connected reductive `G` over a number field `F`;
- a parabolic `p : P → G` with geometric unipotent radical `iU`, rational
  Levi `l` and split component `a`, presented by
  `r : ParabolicRootPresentation p l a`;
- a maximal compact subgroup `K` of `G(𝔸)` with `P(𝔸)K = G(𝔸)` (`hK`);
- a closed matrix embedding `rho` of `G` of size `N > 0` (`hN`, `hrho`);
- the smooth-structure data `hsmooth`, `hcalc`;
- `φ`, an automorphic form on `U(𝔸)M(F) \ G(𝔸)`: `IsAutomorphicFunctionOn`
  for `parabolicQuotientSubgroup F p iU l` and the archimedean part of `K`.

The binders and their order are copied verbatim from that statement.

## Conclusion

There is a real `R₀` with the following property. Let `n` be a natural number,
`e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ` a linear coordinate system, and `W ⊆ ℂⁿ` a bounded
open set. Then there are:

- a real `R` and an open subgroup `L` of `G(𝔸_f)`;
- an index type `Idx : Type u`;
- for each `i ∈ Idx`, a family of continuous linear forms
  `eqn i s : 𝔉^R_L → ℂ` and a family of scalars `c i s ∈ ℂ`, parametrized by
  `s ∈ W`.

`𝔉^R_L` is `UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`. They
satisfy the following, where the system at `s` is `eqn i s v = c i s` for all
`i`, with solution set `systemSolutions eqn c s`:

1. The system is analytic on the open submanifold `W`
   (`IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) eqn c`): every `s ↦ eqn i s v` and
   every `c i` is holomorphic on `W`.
2. The solution sets are locally of finite type
   (`IsLocallyFiniteType 𝓘(ℂ, Fin n → ℂ) (systemSolutions eqn c)`).
3. At every `s ∈ W` such that `e s` is `R₀`-regular
   (`r.IsRegularParameter hA hT R₀ (e s)`), the system has exactly one
   solution `v`. The underlying function of `v` on `G(𝔸)` is the Eisenstein
   series `hK.eisensteinSeries φ (e s)`.
4. At every `s ∈ W`, every solution is an automorphic form on
   `G(F) \ G(𝔸)`: its underlying function satisfies `IsAutomorphicFunctionOn`
   for `rationalSubgroup F G` and the archimedean part of `K`.

`R₀`-regularity is the convergence region of
`EisensteinAbsoluteConvergenceStatement`: `R₀ < B(Re λ|_A, α)` for every
root `α ∈ r.unipotentRoots`. This is the source's region
"`⟨Re λ, α^∨⟩ ≫ 0` for all `α ∈ Δ_P`", in the formulation the convergence and
continuation statements already use.

## Correspondence with the source

- **One system on bounded sets, one Fréchet space.** The source poses one
  system `Ξ_fnl(λ)` for all `λ ∈ 𝔛_P` on `𝔉_umg(X)`, the union of the spaces
  `𝔉^R`. Applying the principle of meromorphic continuation needs a Hausdorff
  locally convex space. The Corollary of §8.6 says that the proof works with
  one `𝔉^R` over each bounded open set. Here the parameter set is a bounded
  open `W` in coordinates `e`, and the space is `𝔉^R_L`, with `R` and `L`
  depending on `W`.
- **The level `L`.** `φ` is right invariant under an open subgroup of
  `G(𝔸_f)`, and so are `E(φ, λ)` and the functions the source's equations
  produce (the operators are convolutions by bi-`K`-finite functions and
  constant terms). Restricting to the right `L`-invariant subspace for such an
  `L` keeps the solutions that matter.
- **Scalar equations.** The source's equations take values in function
  spaces. Following each vector-valued equation by every continuous linear
  form on its target gives a scalar system. Its solution sets are the same,
  by the Hahn–Banach separation theorem in Hausdorff locally convex spaces.
  It is analytic when the original one is, because holomorphy here is weak
  holomorphy (`IsHolomorphicOn` tests continuous linear forms). So the
  statement takes scalar equations indexed by one type `Idx : Type u`.
- **The regularity constant.** The source's region "`≫ 0`" is one region of
  `𝔛_P`, independent of the bounded set. Accordingly `R₀` is chosen before
  `n`, `e` and `W`.
- **Automorphy of solutions.** Item 4 is the step "Lemma 8.1 and equations
  (8.2a) and (8.3) imply that `ψ` is an automorphic form" in the proof of the
  Proposition of §8.4. It holds at every parameter, not only in the regular
  region.

## Provenance

Source statement: Bernstein–Lapid, Proposition of §8.4, with the
automorphy of solutions from its proof (via Lemma 8.1) and the Fréchet
refinement of the Corollary of §8.6. The formulation (bounded parameter sets in
linear coordinates, scalar equations, level `L`) is chosen so that the
principle of meromorphic continuation applies directly, as explained above.
