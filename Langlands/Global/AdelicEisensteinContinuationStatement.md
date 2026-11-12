# Meromorphic continuation of Eisenstein series

Module `Langlands.Global.AdelicEisensteinContinuationStatement` states
`Langlands.Global.EisensteinMeromorphicContinuationStatement` as a
proposition definition. It supplies no proof.

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3 (1), journal p.191 (PDF page 5): in the number field case the
  Eisenstein series `E(φ, λ)`, originally defined and holomorphic for
  `⟨Re λ, α^∨⟩ ≫ 0` for all `α ∈ Δ_P`, extends to a meromorphic function
  `λ ↦ E(φ, λ) ∈ 𝔉_umg(X)` on `𝔛_P`; whenever regular, `E(φ, λ) ∈ 𝒜_G`.
- The Corollary at the end of §8.6, p.226 (PDF page 40): for any bounded open
  `U ⊆ 𝔛_P` there is `R` such that `λ ↦ E(φ, λ)` is meromorphic on `U` with
  values in the Fréchet space `𝔉^R_smth(X)`.
- §3.1, p.192: holomorphic and meromorphic functions with values in a locally
  convex space (local scalar denominators).

## Setting

The hypotheses are those of `EisensteinAbsoluteConvergenceStatement` (module
`Langlands.Global.AdelicEisensteinConvergenceStatement`): a connected
reductive `G` over a number field `F`; a parabolic `p : P → G` with
unipotent radical `iU`, rational Levi `l` and split component `a`, presented
by `r : ParabolicRootPresentation p l a`; a maximal compact subgroup `K` of
`G(𝔸)` with `P(𝔸)K = G(𝔸)` (`hK`); a closed matrix embedding `rho` of `G`
into `GL_N` (`hrho : IsClosedSubgroup rho`) with `N > 0` (`hN`); the
smooth-structure data `hsmooth`,
`hcalc`; and `φ`, an automorphic form on `U(𝔸)M(F) \ G(𝔸)` for the
archimedean part of `K` (MW I.2.17, `IsAutomorphicFunctionOn`). The positivity
of `N` and the closed embedding are premises of the Fréchet spaces.

## Conclusion

There is `E' : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` with the following two properties.

1. **Agreement with the series.** There is `R₀` such that
   `E'(λ) = hK.eisensteinSeries φ λ` (as functions on `G(𝔸)`) for every `λ`
   with `r.IsRegularParameter hA hT R₀ λ`, i.e. `R₀ < B(Re λ|_A, α)` for all
   roots `α ∈ r.unipotentRoots` of `A` in the unipotent radical. This is the region "`⟨Re λ, α^∨⟩ ≫ 0`" of the
   source, expressed with the Weyl-induced form `B` exactly as in the
   convergence statement (whose Markdown explains the equivalence).
2. **Local meromorphy in a Fréchet space, and automorphy.** For every linear
   coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every `s₀ ∈ ℂⁿ` there are an
   open neighborhood `W` of `s₀`, a real `R`, an open subgroup `L` of
   `G(𝔸_f)`, a function `f : W → 𝔉^R_L` and a set `D ⊆ W` such that `f` is
   meromorphic on the open submanifold `W` with domain of holomorphy `D`
   (`IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D` of
   `Langlands.Analysis.Meromorphic.AnalyticSystems`: `D` open and dense in `W`,
   `f` weakly holomorphic on `D`, local scalar denominators), and for every
   `s ∈ D` the underlying function of `f(s)` is `E'(e(s))`, which is an
   automorphic form on `G(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for the
   rational points and the archimedean part of `K`).

`𝔉^R_L` is `UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L` (module
`Langlands.Automorphic.GroupSchemeUniformGrowthFrechet`): the right
`L`-invariant smooth functions on `G(F) \ G(𝔸)` all of whose derivatives are
`O(‖g‖^R)`, with the topology of the seminorms
`sup_g |(a f)(g)| ‖g‖^{-R}`.

## Correspondence with the source

- Theorem 2.3 (1) asserts meromorphy into the union `𝔉_umg(X)`. The
  Corollary of §8.6 refines it: locally (on bounded open sets) the values lie
  in one Fréchet space `𝔉^R_smth(X)` and the function is meromorphic there.
  Since `φ` is `K`-finite, the Eisenstein series have a common level, so one
  of the Fréchet spaces `𝔉^R_L` with `L` open serves. The statement uses this
  local Fréchet formulation. It is the "local common denominators in the
  function-space topology" of the program contract, not a pointwise scalar
  continuation at each group element.
- Meromorphy on `𝔛_P` is expressed in linear coordinates and locally on open
  sets `W`, viewed as open submanifolds of `ℂⁿ` with Mathlib's charted-space
  structure on `TopologicalSpace.Opens`.
- The weight `‖g‖^R` of the adelic norm of the closed embedding `rho`
  replaces BL's `e^{R‖H_0(x)‖}` on a Siegel domain. The Markdown of the
  Fréchet-space module explains why the two families of spaces are expected
  to be mutually cofinal after a change of exponent (MW95 I.2.2 (iv), (vii);
  BL footnote 6, p.211), not equal at the same `R`; that comparison is not
  proved. Since `R` is existential here and chosen locally, as in the
  Corollary of §8.6, the change of exponent does not affect the meaning of
  the statement.
- "Whenever regular, `E(φ, λ) ∈ 𝒜_G`" is required at every point of the
  domain of holomorphy `D`.
- `E'` is unique on the regular points by the identity theorem; uniqueness is
  not asserted.
- The compact subgroup `K` need not be in good position with respect to a
  minimal Levi, as BL assume; the Markdown of the Eisenstein convergence
  statement explains the reduction to their case.

## Scope

Not included: the singularities along root hyperplanes (Theorem 2.3 (6) and
the second form of the Corollary of §8.6), the intertwining operators and
the functional equations (Theorem 2.3 (3)–(5)), the function field case
(Theorem 2.3 (2)), and holomorphy on the imaginary axis (not a result of BL).
