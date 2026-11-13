# Archimedean data of Hecke characters with norm-power archimedean components

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the archimedean factors of the global functional equations of the
characters attached to a relation cancel, because the relation has dimension zero type by type.
In the present setting the global fields are totally real and every character
`Λ = (α ∘ N) · ‖·‖^t · Θ` has the archimedean components of `‖·‖^t` (by
`BrauerKernel.ArchimedeanTrivial`). This unit constructs the archimedean data of the published Hecke
functional-equation package (`HeckeArchData`) for such characters, computes the three
archimedean functions as products over the real places of the base field, and proves their
cancellation. The computation is elementary and has no separate literature source.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Characters

- `realCompletionCharacter_normPower_apply`: at a real place, the archimedean component of
  `‖·‖^t`, read on `ℝ` (`realCompletionCharacter`), is `x ↦ exp(t log |x|)`
  (`normPower_apply`, `coe_ideleClass_infiniteClassInclusion` with multiplicity `1`, and the
  isometry `isometryEquivRealOfIsReal`).
- `realCompletionCharacter_normPower_eq`: these characters of `ℝ^×` agree for all real places of
  all number fields.
- `realCompletionCharacter_inv_eq`: if `Λ` has the component of `‖·‖^t` at a real place, `Λ⁻¹` has
  the component of `‖·‖^{-t}` there.

## Data

Let `M / k` be an extension of number fields with `M` totally real, `ψ` a character of `A_k`
trivial on `k` with real components `a r` (`IsRealAdditiveComponent ψ r (a r)`), and `Λ` a Hecke
character of `M` with the archimedean components of `‖·‖^t`.

- `baseRealData t r`: the polar data (`realCharacterData`) of `|·|^t` read at the real place `r` of
  `k`; `baseRealEpsilon a t r s` is its real epsilon factor for the scale `a r`.
- `normPowerArchData ψ hψ a ha t Λ hΛ : HeckeArchData Λ (traceAdditiveCharacter ψ hψ)`: at a real
  place `u` of `M` over `r`, the additive scale `a r`
  (`isRealAdditiveComponent_traceAdditiveCharacter`) and the polar data `baseRealData (±t) r`; there
  are no complex places.
- `normPowerArchData_A`, `normPowerArchData_Ad`, `normPowerArchData_Ae`: the archimedean
  L-function, dual L-function and epsilon factor of these data are
  `(∏_r den_{t,r}(s)^{[M:k]})⁻¹`, `(∏_r den_{-t,r}(s)^{[M:k]})⁻¹` and `∏_r ε_{t,r}(s)^{[M:k]}`, products
  over the real places of `k` (`prod_realComap`).

## Cancellation

For a finite family `i ∈ S` with weights `e i`, degrees `N i` and pairs of exponents
`(t₁ i, t₂ i)` such that `Σ_i e i · N i · ([t₁ i = τ] - [t₂ i = τ]) = 0` for every `τ`:

- `meromorphicEq_prod_baseRealDenominator`: the product over `i` of the quotients of the
  archimedean L-functions for `t₁ i` and `t₂ i` (each in the form above, with `N i`) raised to
  `e i` has the punctured germ of `1`. Proof: off the discrete set of zeros of the finitely many
  denominators involved (`MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero`), the values are
  units, and `prod_types_pow_eq_one` (`BrauerKernel.ArchimedeanCount`) applies.
- `prod_baseRealEpsilon_eq_one`: the same product of quotients of archimedean epsilon factors is
  `1` at every point (the epsilon factors are units).
