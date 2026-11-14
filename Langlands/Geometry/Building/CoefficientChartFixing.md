# Coefficient charts that fix an apartment point

Author: Worker 47 (Task 6502).

This module extends the published coefficient-chart layer `KPApartmentCoefficientChart`. Let
`A : D.CoefficientChart θ s` be a coefficient chart of a KP apartment datum
`D : KPApartmentData i ω`. It has a correcting element `c`, a character relabelling `β`, an
apartment map `a` and a torus bijection `τ`. The module gives conditions under which `c` is a
normalizer point and the corrected map `x ↦ c • a x` fixes a given apartment point.

## Statements

- `apartment_eq_of_val_eq`: assume there are finitely many relative roots. Let `x`, `y` be
  apartment points such that, for every relative root `α`, there is a point `u` with
  `x_α(u) ≠ ⊤` and `y_α(u) = x_α(u)`. Then `y = x`. Indeed,
  `val_eq_val_add_rootForm` gives `rootForm α (y -ᵥ x) = 0` for all `α`. Then
  `RootTranslationMetric.norm_eq_of_rootForm_equiv` shows that `y -ᵥ x` has the norm of `0`.

Over an infinite field `k`, with `G` connected reductive and `i` a split subtorus, the
remaining statements use the following hypotheses:

- `hθ`: for every `t ∈ S(k)` there is `t'` with `θ(i t) = i t'` and
  `s(χ(t')) = χ(t)` for all characters `χ`. That is, `θ` acts on the torus compatibly with
  `s⁻¹` on character values.
- `hθ'`: `θ` maps `i(S(k))` onto `i(S(k))`.
- `hroot` (for an apartment point `x`): every relative root `α` has a point `u` with
  `x_α(u) ≠ ⊤` and `θ u = u`.

The statements:

- `c_mem_normalizerPoints`: assuming the first half of `hθ` and `hθ'`, `A.c` is a normalizer
  point. Conjugation by `A.c` preserves `i(S(k))` in both directions, by the chart's torus
  field. Then apply `mem_normalizerPoints_of_conj`.
- `smul_a_eq`: under `hθ`, `hθ'` and `hroot`, `⟨A.c, _⟩ • A.a x = x`. Write `n` for `A.c`
  viewed as a normalizer point.
  1. `A.β (weylAction i n⁻¹ b) = b` for every character `b`. Both sides take the same values on
     `S(k)`, by the chart's character field, `weylAction_torusCharacterValue` and `hθ`. Then
     apply `torusCharacterValue_injective`.
  2. Hence `(n • A.a x)_b(θ u) = x_b(u)`, using `RootFunctionFamily.smul_apply` and the chart's
     transport formula.
  3. Evaluating at the `θ`-fixed points from `hroot` and applying `apartment_eq_of_val_eq`
     gives the claim.
- `c_smul_apartment_a_eq`: the same statement on the reduced building,
  `A.c • [a x] = [x]`, obtained through `ApartmentQuotient.apartment_smul`.

## Provenance

This is internal infrastructure. It is the chart-level form of the standard fact that a
semilinear automorphism of the coefficients fixes the apartment of a torus pointwise when it
acts on that torus "as on the coefficients" and fixes a nontrivial element of every root group.
It is used for the finite orbits of the Galois action on the unramified building (Task 6502).
