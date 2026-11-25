# Proof: pointwise representatives of integrated translation actions

`Langlands.Analysis.integratedTranslationPointwise` proves
`Langlands.Analysis.IntegratedTranslationPointwiseStatement.{uX, uG}`, with
two independent universes. The module imports only the public target
statement and Mathlib.

## Route

1. The proof replaces the weight `f` by the strongly measurable version
   `f' := hf.aestronglyMeasurable.mk f`, which agrees with `f` almost
   everywhere and is again integrable. It uses Mathlib's strongly measurable
   representative of the `L²` class `φ` (`Lp.stronglyMeasurable`). The
   product integrand `Φ (x, g) = f' g * φ (act x g)` is then strongly
   measurable, by joint measurability of the action.
2. Fix a measurable set `B` of finite measure. Hölder's inequality
   (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) and measure preservation of
   each translate (`eLpNorm_comp_measurePreserving`) give
   `∫⁻ x in B, ‖φ (act x g)‖ₑ ≤ μX(B)^{1/2} · ‖φ‖₂` for every `g`.
   Tonelli (`lintegral_lintegral_swap`) then bounds the absolute double
   integral of `Φ` over `B × G` by `μX(B)^{1/2} · ‖φ‖₂ · ∫⁻ ‖f'‖ₑ`, which is
   finite. Hence `Φ` is integrable for `(μX.restrict B).prod μ`.
3. Part (a) follows: on each such `B`, almost every slice integral
   `∫⁻ g, ‖Φ (x, g)‖ₑ` is finite, and σ-finiteness of `μX` removes the
   restriction to `B` (`ae_of_forall_measure_lt_top_ae_restrict`). Since
   `f = f'` almost everywhere, integrability transfers from
   `g ↦ f' g * φ (act x g)` to `g ↦ f g * φ (act x g)`.
4. For part (b), both sides are first rewritten with `f'` in place of `f`:
   the pointwise integral by `integral_congr_ae`, and
   `integratedIsometricAction` through `integratedIsometricAction_apply`
   and `integral_congr_ae`. The proof then applies
   `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`. Both sides are
   integrable on finite-measure sets: the `L²` class by
   `integrableOn_Lp_of_measure_ne_top`, the pointwise integral by the bound
   of step 2. Their set integrals over `B` agree, by a chain of four
   rewrites:
   - `L2.inner_indicatorConstLp_one` writes the left side as an inner
     product with the indicator of `B`;
   - `integral_inner` (with the integrability lemma
     `isometricActionIntegrand_integrable`) moves that inner product inside
     the Bochner integral;
   - the compatibility hypothesis identifies each translate `π g φ` with
     `x ↦ φ (act x g)` on `B`;
   - `integral_const_mul` and Fubini (`integral_integral_swap`, using the
     integrability from step 2) give the right side.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are
used.

## Provenance

The argument is the standard Fubini–Tonelli identification of a
vector-valued (Bochner) integral in `L²` with the pointwise integral of
representatives, tested against indicators of finite-measure sets; it is
internal to this project and follows no particular literature proof. This
Markdown names each step of that proof.
