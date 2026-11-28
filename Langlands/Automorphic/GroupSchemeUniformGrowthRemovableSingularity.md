# Removable singularities of quotients in the spaces of uniform moderate growth

Module `Langlands.Automorphic.GroupSchemeUniformGrowthRemovableSingularity`. Two scalar lemmas
on Taylor coefficients (namespace `Langlands.Analysis`) and two results on the Fréchet spaces
`𝔉^R_L = UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L` of uniform moderate
growth (namespace `Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace`).
Everything is proved; there are no premises.

## Purpose and provenance

Provenance: internal. A meromorphic `𝔉^R_L`-valued function `f = num / den` (Bernstein–Lapid
2024, §3.1) may have scalar evaluations `s ↦ f(s)(g)` that are holomorphic at a point `s₀` for
every `g ∈ G(𝔸)`, although `den(s₀) = 0`. The main theorem shows that `f` then extends near
`s₀` to a weakly holomorphic `𝔉^R_L`-valued function, so the scalar holomorphy of all point
evaluations controls every seminorm of `𝔉^R_L` near `s₀`. Point evaluations separate the
vectors of `𝔉^R_L` (`toFun_injective`), and the proof combines this with the Taylor
coefficients of curves in `𝔉^R_L` (`taylorCoefficient`, module
`Langlands.Automorphic.GroupSchemeUniformGrowthTaylor`) and the circle division of
`Langlands.Analysis.SeveralComplex.HolomorphicSliceDivision`. The argument follows the line
detection of `Langlands.Global.AdelicTaylorPoleDetection` and the uniform transfer of
`Langlands.Global.AdelicPoleTransfer`, with point evaluations, which separate all vectors, in
place of tests that separate automorphic forms; no automorphy is assumed.

## Scalar lemmas

- `iteratedDeriv_eq_factorial_mul_of_eventuallyEq_pow_mul`: if `φ(t) = t^k h(t)` near `0` with
  `h` analytic at `0`, then `φ^{(k)}(0) = k! h(0)`. Proof: replace `φ` by `t^k h(t)`
  (`Filter.EventuallyEq.iteratedDeriv_eq`), apply the Leibniz rule `iteratedDeriv_fun_mul`; by
  `iteratedDeriv_pow` only the term `i = k` survives.
- `iteratedDeriv_eq_mul_of_analyticOrderAt_eq`: let `ψ` and `χ` be analytic at `0`, `ψ` of
  analytic order exactly `k` at `0`, and `φ = ψ χ` near `0`. Then
  `φ^{(k)}(0) = ψ^{(k)}(0) χ(0)` and `ψ^{(k)}(0) ≠ 0`. Proof: write `ψ(t) = t^k g(t)` with
  `g(0) ≠ 0` (`AnalyticAt.analyticOrderAt_eq_natCast`) and apply the previous lemma to `ψ` and
  to `φ = t^k (g χ)`.

## `analyticallyDividesAt_of_eval`

Let `L` be open, `U ⊆ ℂ` open and `f : ℂ → 𝔉^R_L` weakly holomorphic on `U` (every continuous
linear form composed with `f` is holomorphic on `U`). Let `z ∈ U` and `den` be analytic at `z`
of finite order. If `den` divides every point evaluation `t ↦ f(t)(g)` analytically at `z`
(`AnalyticallyDividesAt`), then it divides `t ↦ test (f t)` analytically at `z` for every
continuous linear form `test`.

Proof. Let `m` be the order of `den` at `z`. Each point evaluation has order at least `m`, so
its derivatives of order `k < m` vanish at `z`. The Taylor vector `a_k = taylorCoefficient … k
z ∈ 𝔉^R_L` satisfies `test (a_k) = (test ∘ f)^{(k)}(z) / k!` for every continuous linear form
(`apply_taylorCoefficient`). For the point evaluations (`UniformGrowthFrechetSpace.evalCLM`)
this vanishes, so the underlying function of `a_k` is zero and `a_k = 0` (`toFun_injective`).
Hence `(test ∘ f)^{(k)}(z) = 0` for all `k < m`, the order of `test ∘ f` at `z` is at least `m`,
and `analyticallyDividesAt_of_order_le` gives the division.

## `exists_weaklyHolomorphic_of_mul_eq_eval`

Let `E` be a finite-dimensional complex normed space, `L` open, `U ⊆ E` open and `s₀ ∈ U`. Let
`num : E → 𝔉^R_L` be weakly holomorphic on `U`, `den : E → ℂ` holomorphic on `U` and not
identically zero near `s₀`, and `Φ : E → G(𝔸) → ℂ` with `s ↦ Φ s g` holomorphic on `U` for
every `g`, such that `num(s)(g) = den(s) Φ(s)(g)` for all `s ∈ U` and `g`. Then there are an
open `V` with `s₀ ∈ V ⊆ U` and `v : E → 𝔉^R_L`, weakly holomorphic on `V`, whose underlying
function `v(s)` is `Φ s` for every `s ∈ V`.

Proof as implemented.

1. `exists_open_division_circle` gives a direction `u`, a radius `0 < r < 2` and an open
   `V ∋ s₀` such that for `s ∈ V` the disc `{s + t u : |t| < 2}` lies in `U` and `den` does not
   vanish on the circle `|t| = r`. On each such slice `den` has finite order at every point of
   the disc (it is analytic on the connected disc and nonzero at `t = r`).
2. On the slice through `s ∈ V` each point evaluation of `num` is `den` times the analytic
   function `t ↦ Φ (s + t u) g`, so `analyticallyDividesAt_of_eval` gives analytic division of
   `t ↦ test (num (s + t u))` by `t ↦ den (s + t u)` at every point of the disc, for every
   continuous linear form `test`.
3. The circle averages `b_test = circleDivision den (test ∘ num) u r` are holomorphic on `V`
   (`differentiableOn_circleDivision`) and satisfy `den(s) b_test(s) = test (num s)` on `V`
   (`mul_circleDivision_eq`).
4. For `s ∈ V` let `k` be the order at `0` of `d(t) = den(s + t u)` and put
   `v(s) = (d^{(k)}(0) / k!)⁻¹ • a_k`, where `a_k` is the `k`-th Taylor vector of
   `t ↦ num (s + t u)` at `0`. If `test (num (s + t u)) = d(t) χ(t)` near `0` with `χ`
   analytic at `0`, then by `apply_taylorCoefficient` and the second scalar lemma
   `test (v s) = χ(0)`.
5. With `χ(t) = b_test (s + t u)` (step 3) this gives `test ∘ v = b_test` on `V`, so `v` is
   weakly holomorphic on `V`. With `test` the evaluation at `g` and `χ(t) = Φ (s + t u) g` it
   gives `v(s)(g) = Φ s g`.
