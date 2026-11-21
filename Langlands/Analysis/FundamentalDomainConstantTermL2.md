# Fibre averages are contractions of weighted `L²` norms

Module `Langlands.Analysis.FundamentalDomainConstantTermL2`, namespace
`Langlands.Analysis.FibreAverage`. It builds on
`Langlands.Analysis.FundamentalDomainFibreAverage` and uses the same data: a measurable group
`H` with left-invariant `μ`, a countable `Λ ≤ H` with a strict measurable fundamental domain
`D`, an injective measurable homomorphism `j : V → H`, a subgroup `Γ ≤ V` with `j(Γ) ⊆ Λ`,
conjugations `cj l` that preserve `ν` and `Γ`, and a measurable fundamental domain `C` of `Γ`
in `V`.

## Definitions

- `foldElement Λ hD x` is the unique `l ∈ Λ` with `l x ∈ D`, and `fold Λ hD x = l x` is the
  representative of the orbit `Λ x` in `D`. Proved properties: `fold` is measurable
  (`measurable_fold`, through `fold_preimage`, which writes preimages as a countable union of
  translates), `fold (l x) = fold x` for `l ∈ Λ` (`fold_mul_left`), and `fold x = x` on `D`
  (`fold_of_mem`). For a function `f` given on `D`, `f ∘ fold` is its `Λ`-invariant extension.
- `foldConstantTerm Λ D hD j ν C f g = ν(C)⁻¹ ∫_C f(fold(j v · g)) dν(v)` is the constant term of
  `f` along `j V` for the normalized measure on `C`. For `H = G(𝔸)`, `Λ = P₀(F)`, `V = U_P(𝔸)` and
  `Γ = U_P(F)` it is BL's `CT_P` (Bernstein–Lapid, J. Amer. Math. Soc. 37 (2024), §7.3, p.214)
  applied to the `P₀(F)`-invariant extension of `f`. The definition uses the fundamental domain
  `C` instead of quotient representatives (`Quotient.out`), so the integrand is jointly
  measurable in `(v, g)`.

## Main statement

`FoldConstantTermContractionStatement`, proved by `foldConstantTermContraction` (equivalently
`setLIntegral_foldConstantTerm_le`). Assume in addition `0 < ν C < ∞`. Let `f : H → ℂ` be
measurable and let `W : H → [0, ∞]` be measurable with `W(l x) = W(x)` for `l ∈ Λ` and
`W(j v · x) = W(x)` for `v ∈ V`. Then

`∫_D ‖foldConstantTerm f‖² W dμ ≤ ∫_D ‖f‖² W dμ`.

In the application, `W` is the weight `w_λ⁻²` times the indicator of the Siegel domain. Both
depend only on the height `H₀`, which is invariant under `U_P(𝔸)` on the left and under
`P₀(F)`, so `CT_P` is a contraction of BL's weighted space `H^λ` (§7.3–7.4, pp.214–215).

## Proof

1. *Jensen* (`sq_lintegral_le_lintegral_sq`): for a probability measure `P`,
   `(∫ a dP)² ≤ ∫ a² dP`. This is Hölder's inequality (`ENNReal.lintegral_mul_le_Lp_mul_Lq`)
   with exponents `2, 2` against the constant `1`.
2. *Pointwise bound* (`enorm_foldConstantTerm_sq_le`): with `P = ν(C)⁻¹ ν|_C`, the norm of the
   Bochner integral is at most the integral of the norm, and Jensen gives
   `‖CT f (g)‖² ≤ ν(C)⁻¹ ∫_C ‖f(fold(j v g))‖² dν`.
3. *Integration.* Multiply by `W(g) = W(j v g)` and integrate over `D`. The function
   `F = ‖f ∘ fold‖² · W` is `Λ`-invariant. The fibre-average identity
   (`setLIntegral_fibreAverage`) gives `∫_D ∫_C F(j v g) = ν(C) ∫_D F`, and `fold = id` on `D`.

## Scope

Only the inequality is proved. The bounded operator on `L²`, its compatibility with almost
everywhere equality, the composition rule `CT_R CT_Q = CT_{R ∩ Q}` and the adelic instantiation
are separate steps on the route to Bernstein–Lapid Theorem 7.2.
