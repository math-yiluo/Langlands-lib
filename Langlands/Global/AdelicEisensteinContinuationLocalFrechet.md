# Local Fréchet representations of Eisenstein continuations

Module `Langlands.Global.AdelicEisensteinContinuationLocalFrechet` derives three consequences
of the meromorphic continuation of Eisenstein series in the Fréchet form of
`EisensteinMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicEisensteinContinuationStatement`; Bernstein–Lapid 2024, Theorem 2.3 (1)
and the Corollary of §8.6) for an arbitrary pointwise continuation. The first one takes that
statement as an explicit hypothesis `hMero`; the module proves no continuation.

| Declaration | Kind | Provenance |
| --- | --- | --- |
| `Langlands.Analysis.Meromorphic.IsMeromorphicOn.mono_of_isOpen_of_dense` | theorem | internal |
| `continuousOn_of_local_frechet` | theorem | internal |
| `exists_isMeromorphicOn_rightConvolution` | theorem | internal |
| `exists_local_frechet_of_eisensteinContinuation` | theorem | derived from BL Theorem 2.3 (1), Corollary 8.6 |

Notation: `𝔉^R_L = UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`, the Fréchet
space of functions of uniform moderate growth of exponent `R` and level `L`, and `toFun` its map
to functions on `G(𝔸)`. A *pointwise continuation* of the Eisenstein series `E(φ, ·)` is a
function `E : X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` with a set `D` such that every `λ ↦ E λ g` is meromorphic
in linear coordinates with domain of holomorphy `D` (`IsMeromorphicInCoordinatesOn`), and
`E λ = hK.eisensteinSeries φ λ` for `R`-regular `λ`, for some `R`.

## Results

- `IsMeromorphicOn.mono_of_isOpen_of_dense`: on a complex manifold, a meromorphic function with
  domain of holomorphy `U` is meromorphic with every open dense `U' ⊆ U` as domain. The local
  quotients are those for `U`.
- `continuousOn_of_local_frechet`: let `f : W → 𝔉^R_L` be meromorphic on an open
  `W ⊆ ℂᵐ` with domain of holomorphy `Df`, and let `Φ : ℂᵐ → (G(𝔸) → ℂ)` satisfy
  `toFun (f t) = Φ t` for `t ∈ Df`. Suppose `s ↦ Φ s g` is complex differentiable on an open
  `O` for every `g`. Then every `s₀ ∈ W ∩ O` has an open neighbourhood `T ⊆ O` on which
  `(s, g) ↦ Φ s g` is continuous on `T × G(𝔸)`.

  Proof as implemented. Take the local quotient `g • f = h` of `f` near `s₀`, on a connected
  open `W'`, and extend `g` and `h` by zero to `ℂᵐ` (`extendOpens`). Let `T` be a ball around
  `s₀` inside `W' ∩ O`. The extended `g` is differentiable on `T` and not identically zero there
  (`exists_ne_zero_of_differentiableOn`, since `g` is not identically zero on the connected
  `W'`). Every scalar continuous linear form of the extended `h` is differentiable on `T`. For
  `s` in the dense part `T ∩ (Df ∩ W')`, evaluation at `y` gives
  `g(s) Φ s y = toFun (h s) y`. Both sides are continuous in `s` on `T`, so the identity holds
  on `T` (`EqOn.of_subset_closure`). The Library's
  `UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval` (module
  `Langlands.Automorphic.GroupSchemeUniformGrowthJointEvaluation`) then gives joint
  continuity on `T × G(𝔸)`.
- `exists_isMeromorphicOn_rightConvolution`: if `Φ` has local representations as in the
  previous item near every point of `ℂᵐ`, and `ψ` is continuous with compact support, then
  there is one set `U` such that every `s ↦ rightConvolution F G ψ (Φ s) g` is meromorphic on
  `ℂᵐ` with domain of holomorphy `U`. Proof: evaluate the local `𝔉^R_L`-valued functions at
  the continuous linear forms `rightConvolutionEvalCLM` (module
  `Langlands.Global.AdelicEisensteinScalarEquations`), which are `v ↦ R(ψ) v (g)`, through
  `hasLocalMeromorphicData_of_isMeromorphicOn`, and glue with
  `exists_isMeromorphicOn_of_local` (module `Langlands.Analysis.Meromorphic.CoordinateGluing`).
- `exists_local_frechet_of_eisensteinContinuation`: assume `hMero`, `G` connected reductive,
  `iU` a geometric unipotent radical, `N > 0`, `rho` closed, `K` maximal compact with
  `hK : IsIwasawaCompact p K`, and `φ` automorphic on `U(𝔸) M(F) \ G(𝔸)`. Then for every
  pointwise continuation `(E, D)` of `E(φ, ·)`, every linear chart
  `e₀ : ℂᵐ ≃ X^*(P) ⊗ ℂ` and every `s₀ ∈ ℂᵐ`, there are an open `W ∋ s₀`, `R`, `L`, and a
  meromorphic `f : W → 𝔉^R_L` with domain `Df` such that `toFun (f t) = E (e₀ t)` for `t ∈ Df`.

  Proof as implemented. `hMero` gives a continuation `Ea` with the regular agreement and local
  `𝔉^R_L`-valued representations. Evaluating them at points (`uniformGrowthEvalCLM`) and gluing
  in the chart `e₀`, as in the Library's `exists_glued_eisensteinContinuation`, makes every
  `λ ↦ Ea λ g` meromorphic in coordinates with domain `e₀ '' U₀`. `E` and `Ea` agree with the
  Eisenstein series on a common regular region (`isRegularParameter_mono`), so they agree on
  `D ∩ e₀ '' U₀` (`ParabolicRootPresentation.eqOn_of_regularParameter`, the identity theorem
  in coordinates). Restrict the representation `f` of `Ea` near `s₀` to the open dense part of
  its domain where `e₀ t ∈ D ∩ e₀ '' U₀` (`mono_of_isOpen_of_dense`); there `toFun (f t) =
  Ea (e₀ t) = E (e₀ t)`.

## Provenance

The first three results are internal complex analysis on the Library's meromorphy notions
(Bernstein–Lapid §3.1). The last applies Theorem 2.3 (1) and the Corollary of §8.6 of
J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, through the Library statement
`EisensteinMeromorphicContinuationStatement`, to continuations given only pointwise. The
module contains no proof of that statement.
