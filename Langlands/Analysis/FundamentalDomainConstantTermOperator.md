# The constant term as a contraction of weighted `L²`

Module `Langlands.Analysis.FundamentalDomainConstantTermOperator`, namespace
`Langlands.Analysis.FibreAverage`. It uses the data of
`Langlands.Analysis.FundamentalDomainFibreAverage` and the folded constant term
`foldConstantTerm` of `Langlands.Analysis.FundamentalDomainConstantTermL2`, with `0 < ν C < ∞`
and a measurable weight `W : H → [0, ∞]` such that `W(l x) = W x` for `l ∈ Λ` and
`W(j v · x) = W x` for `v ∈ V`.

## Definitions

- `weightedMeasure μ D W = (μ|_D).withDensity W`. For `H = G(𝔸)` and `Λ = P₀(F)`, `L²` of this
  measure is `L²(P₀(F)\G(𝔸))` for the density `W`, through the strict fundamental domain `D`.
  With `W = w_λ⁻² · 1_S` it is Bernstein–Lapid's weighted space on the Siegel domain (§§7.3–7.4,
  pp.214–215).
- `rep μ D W F` is a strongly measurable representative of `F ∈ L²` (Mathlib's
  `AEStronglyMeasurable.mk`).
- `foldConstantTermLp` is the `L²` class of `foldConstantTerm (rep F)`.
- `foldConstantTermCLM` is the same map, bundled as a continuous linear operator on
  `L²(W · μ|_D)` with the bound `1` (`LinearMap.mkContinuous`).

## Statement

`FoldConstantTermOperatorStatement`, proved by `foldConstantTermOperator`. Under the hypotheses
above there is a continuous linear operator `T` on `L²((μ|_D).withDensity W)` with `‖T‖ ≤ 1` and
`T F = foldConstantTerm f` almost everywhere for every measurable `f` that agrees almost
everywhere with `F`. The operator is `foldConstantTermCLM`. Its properties are
`norm_foldConstantTermCLM_le` and `foldConstantTermCLM_ae`.

## Proof

1. `setLIntegral_fibre_sq_mul`: for measurable `f`,
   `∫_D (∫_C ‖f(fold(j v g))‖² dν) W(g) dμ = ν(C) ∫_D ‖f‖² W dμ`. This is the fibre-average
   identity applied to the `Λ`-invariant function `‖f ∘ fold‖² · W`, using
   `W(j v g) = W(g)` and `fold = id` on `D`.
2. `ae_integrableOn_fibre`: if `f` has finite weighted norm, the left side of step 1 is finite.
   So for almost every `g` for the weighted measure, `v ↦ f(fold(j v g))` is square integrable on
   `C`, hence integrable, because `ν(C) < ∞`.
3. `foldConstantTerm_add` and `foldConstantTerm_smul` give pointwise linearity where the fibres
   are integrable. With step 2 this gives additivity almost everywhere
   (`foldConstantTerm_ae_add`).
4. `stronglyMeasurable_foldConstantTerm`: the integrand is jointly measurable, so the fibre
   integral is strongly measurable in `g` (`StronglyMeasurable.integral_prod_right`).
5. `eLpNorm_foldConstantTerm_le` is the norm form of `setLIntegral_foldConstantTerm_le`, via
   `lintegral_weightedMeasure`.
6. `foldConstantTerm_ae_congr`: if `f = f'` almost everywhere, then `f − f'` has norm zero, so
   by step 5 its constant term has norm zero. By step 3 the constant terms of `f` and `f'` then
   agree almost everywhere. Hence the operator does not depend on the representative.
7. Additivity, homogeneity and the bound of the operator follow from steps 3, 5 and 6, together
   with `Lp.coeFn_add`, `Lp.coeFn_smul` and `MemLp.coeFn_toLp`.

## Scope

The module does not prove idempotence or self-adjointness, the composition rule
`CT_R CT_Q = CT_{R ∩ Q}`, commutation with translations, or the adelic instantiation. It also
does not identify the space with the weighted automorphic stage on the quotient. These are later
steps on the route to Bernstein–Lapid Theorem 7.2.
