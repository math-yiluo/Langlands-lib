# Iterated integrals against an arbitrary measure

The module `Langlands.Analysis.FamilyLIntegral` proves Tonelli-type inequalities in which the outer
measure `m` on the index space `Ω` of a family is arbitrary, possibly not σ-finite. They are used to
integrate estimates for families of functions over an arbitrary measure space, as in the family
estimate (13.5)–(13.6) of Arthur's *An introduction to the trace formula* (2005), Proposition 13.2(b).
All declarations are in `Langlands.Analysis`.

## Averages against a finite measure

`lintegral_lintegral_le_mul_iSup`: let `ν` be a finite measure on `X`, `m` any measure on `Ω` and
`F : Ω → X → ℝ≥0∞` jointly measurable. Suppose a countable set `D ⊆ X` detects vanishing: if
`F o` vanishes on `D`, it vanishes identically. Then

`∫_Ω ∫_X F(o, x) dν(x) dm(o) ≤ ν(X) · sup_x ∫_Ω F(o, x) dm(o)`.

**Proof.** The inequality is trivial if `ν = 0` or if the supremum `M` is infinite. Otherwise let
`S` be the set of `o` with `F(o, x) ≠ 0` for some `x ∈ D`. Outside `S` the inner integral vanishes,
so the left side is the same integral against `m` restricted to `S`. This restriction is σ-finite:
`S` is covered by the countably many sets `{o : F(o, x) ≥ 1/(k + 1)}`, `x ∈ D`, `k ∈ ℕ`, and each
has `m`-measure at most `(k + 1) M < ∞` by Markov's inequality. Tonelli's theorem for
`m|_S × ν` exchanges the integrals, and each inner integral `∫ F(·, x) dm|_S` is at most `M`.

`lintegral_lintegral_le_mul_iSup_of_ae` is the variant for a finite measure `ν` concentrated on a
set `T`, with `D ⊆ T`, vanishing detected on `T` only, and the supremum taken over `x ∈ T`.

## A fundamental theorem of calculus for families

`lintegral_enorm_sub_le_iSup_deriv`: if `f o` has derivative `f' o t` at every `t`, each `f' o` is
continuous and `(o, t) ↦ f' o t` is jointly measurable, then

`∫_Ω ‖f o 1 − f o 0‖ dm ≤ sup_{t ∈ [0, 1]} ∫_Ω ‖f' o t‖ dm`.

`lintegral_enorm_sub_le_iSup_of_integral` has the same conclusion under the integrated hypothesis
`f o 1 − f o 0 = ∫₀¹ f' o t dt`. In both, the pointwise bound `‖f o 1 − f o 0‖ ≤ ∫₀¹ ‖f' o t‖ dt`
is integrated over `Ω` with `lintegral_lintegral_le_mul_iSup` for Lebesgue measure on `[0, 1]`
(through the projection onto `[0, 1]`); the rationals detect vanishing of the continuous functions
`t ↦ ‖f' o t‖`.
