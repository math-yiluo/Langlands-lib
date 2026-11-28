# Siegel bounds for unitary exponent sums on Levi chambers

Module `Langlands.Global.AdelicWeakConstantTermChamberExtrapolation`. All results are proved.
The main theorem, `StandardParabolicFamily.exists_leviChamber_bound_of_unitaryExponents`,
extends the logarithmic Siegel chamber bound of a function on `G(𝔸)` from the chamber of `G`
to the larger chamber defined by the simple roots of a standard Levi only, when the function is
a sum of terms with unitary exponents along the standard parabolic.

| Declaration | Kind | Content |
| --- | --- | --- |
| `Langlands.Analysis.norm_le_of_monic_translationSolution` | theorem | growth along a translation equation with a monic polynomial whose roots have norm `≤ κ` |
| `siegelModulus_pos`, `siegelModulus_mul`, `sqrt_siegelModulus_pow_mul` | theorems | the Siegel modulus is positive and multiplicative; `δ(rⁿ b)^{1/2} = δ(r)^{n/2} δ(b)^{1/2}` |
| `AdelicGroupPoints.characterLog_pow`, `characterLog_comp` | theorems | `log|χ(xⁿ)| = n log|χ(x)|`; `log|(j ≫ χ)(x)| = log|χ(j(x))|` |
| `exists_abs_characterLog_le` | theorem | `|log|χ(g)|| ≤ c₀ + c₁ log H(g)` for a closed matrix embedding |
| `StandardParabolicFamily.exists_splitComponent_siegelRay` | theorem | a split ray of `P_J` in the Siegel torus |
| `StandardParabolicFamily.adelicHeight_positiveMap` | theorem | the height of a Siegel torus point read through the maximal split torus |
| `StandardParabolicFamily.exists_ray_shift_mem_chamber` | theorem | shifting a point of the `J`-chamber into the chamber of `G` along the ray |
| `StandardParabolicFamily.log_adelicHeight_ray_shift_le` | theorem | the logarithmic height grows at most linearly along the ray |
| `StandardParabolicFamily.exists_leviChamber_bound_of_unitaryExponents` | theorem | the main bound |

## Translation equations

`norm_le_of_monic_translationSolution`: let `a` be an element of a monoid `A`, `D ∈ ℂ[X]` monic
with every complex root of norm at most `κ > 0`, and `φ : A → ℂ` with
`∑_k D_k φ(a^k g) = 0` for every `g`. If `M ≥ 0` and `‖φ(a^j g)‖ ≤ κ^j M` for `j < deg D`, then
`‖φ(a^q g)‖ ≤ 3^{deg D} (q + 1)^{deg D} κ^q M` for every `q`. Over `ℂ` the monic `D` is the
product of `X - z` over its roots (`prod_multiset_X_sub_C_of_monic_of_roots_card_eq`), and the
published `Langlands.Analysis.norm_le_of_translationSolution` applies to the list of roots.

## The main theorem

Notation: `fam` is a standard parabolic family of `G`, `(fam.T, fam.i, fam.ν, T₀, j)` an
algebraic Siegel setup of `G`, `a_G = positiveMap F G fam.T fam.i T₀ j`, `δ = siegelModulus` of
that setup, `H = adelicHeight F G rho` for a closed matrix embedding `rho` of size `N > 0`, `J`
a standard index and `P = P_J`.

`exists_leviChamber_bound_of_unitaryExponents`: assume
`StandardNestedHalfModulusCompatibilityStatement`. Let `s` be a finite set of complex
parameters of `P` and `c_λ : G(𝔸) → ℂ` functions such that each `c_λ` has the normalized
exponent `λ` along `P` (`fam.HasExponent J λ (c λ)`) and `Re λ = 0`
(`parameterRealPart = 0`), and let `ψ = ∑_{λ ∈ s} c_λ` satisfy the logarithmic Siegel chamber
bound `fam.HasSiegelChamberGrowth j rho ψ`. Then for every threshold `t` and compact
`Ω ⊆ G(𝔸)` there are `e : ℕ` and `B ≥ 0` such that

`‖ψ(a_G(b) w)‖ ≤ B δ(b)^{1/2} (1 + log H(a_G(b)))^e`

for every `w ∈ Ω` and every `b ∈ A_{T₀}` with `log t ≤ log|β(b)|` for the simple roots `β ∈ J`
only. No condition is imposed on the simple roots outside `J`.

### Proof

1. *A split ray* (`exists_splitComponent_siegelRay`). The product `r` of the fundamental rays
   `exists_siegelFundamentalRays` of the simple roots outside `J` satisfies
   `log|β(r)| = 0` for `β ∈ J` and `log|α(r)| > 0` for the other simple roots, and `a_G(r)` is
   the image of a point `a_D` of the positive split component `𝔄_P`. The product is built by
   induction over a finite set of simple roots.
2. *Equations with unitary roots.* By `HasExponent.exists_isTranslationPolynomialSolution_pow`,
   applied to `a_D⁻¹ ∈ 𝔄_P`, each `c_λ` satisfies the translation equation along `a_D⁻¹` with
   polynomial `(X − (a_D⁻¹)^{λ + ρ_P})^{k_λ + 1}`; `isTranslationPolynomialSolution_sum_prod`
   gives the product equation for `ψ`. Since `Re λ = 0`, `|(a_D⁻¹)^λ| = 1`, and
   `|(a_D⁻¹)^{ρ_P}| = |a_D^{ρ_P}|⁻¹ = δ(r)^{-1/2}` by
   `halfModulus_eq_siegelSqrt_of_positiveSplitComponent`. So every root of the product
   polynomial has norm `κ = δ(r)^{-1/2}`.
3. *Shifting into the chamber* (`exists_ray_shift_mem_chamber`). With
   `|log|α(b)|| ≤ c₀ + c₁ log H(a_G(b))` (`exists_abs_characterLog_le` for `fam.i ≫ rho`), there
   are `X₀, X₁ ≥ 0` and for each such `b` an `n₀ ≤ X₀ + X₁ log H(a_G(b))` such that `rⁿ b` lies
   in the weak chamber of `G` of threshold `t` for all `n ≥ n₀`: the roots in `J` do not change
   along `r`, and the other simple roots grow linearly in `n`.
4. *Extrapolating back.* Put `Q = deg + n₀` and `g' = a_G(r)^Q a_G(b) w`. For `j < deg` the
   point `(a_D⁻¹)^j g'` is `a_G(r^{Q−j} b) w` with `Q − j ≥ n₀`, where the chamber bound and
   `δ(r^n b)^{1/2} = δ(r)^{n/2} δ(b)^{1/2}` give `‖ψ‖ ≤ κ^j M` with
   `M = C δ(r)^{Q/2} δ(b)^{1/2} (c₂ (1 + log H(a_G(b))))^{e₀}`; the heights along the ray are
   controlled by `log_adelicHeight_ray_shift_le`. The translation bound at `q = Q` gives
   `‖ψ(a_G(b) w)‖ ≤ 3^{deg} (Q + 1)^{deg} κ^Q M`, where `κ^Q δ(r)^{Q/2} = 1` and
   `Q + 1 ≤ (c₃ + 1)(1 + log H(a_G(b)))`.

## Sources

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering): Proposition 3.6 and
Definition 3.7, p. 13, and Lemma 3.8 (ii), p. 14. Delorme obtains the bound on the Levi from
temperedness on `M` via Proposition 3.6 (sufficiency, attributed to Mœglin–Waldspurger I.4.1).
The route here is derived: it uses the chamber bound on `G` and the unitarity of the exponents
along the split component, and extrapolates along a ray of `𝔄_P` with the exponential-polynomial
growth estimate of `Langlands.Analysis.norm_le_of_translationSolution`.
