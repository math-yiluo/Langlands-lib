# Norm-one orbital integrals of tensors with three prescribed local factors

The module works in the norm-one subgroup `H` of the adelic points of a group scheme `G` over
a number field `K`, with the identity twist, and with Borel σ-algebras on all left quotients.

## Measures and positivity

* `twistedOrbitalIntegral_ne_zero_iff_of_isCompatible`: two compatible choices of a right
  Haar measure on the twisted centralizer and of a quotient measure differ by one positive
  scalar (`exists_eq_smul_of_isMulRightInvariant` and `IsCompatible.smul_eq_smul`), so the
  orbital integrals of a function for the two choices vanish together.
* `twistedOrbitalIntegral_ne_zero_of_re_nonneg`: a continuous function with nonnegative real
  part that is positive at the base point and has integrable orbit function has nonzero
  orbital integral. The orbit function is continuous, and a compatible quotient measure is
  positive on nonempty open sets (`IsCompatible.isOpenPosMeasure`).
* `normOnePositiveAverage_re_nonneg` and `normOnePositiveAverage_re_pos`: the average over the
  positive central subgroup preserves nonnegativity of the real part, and preserves positivity
  at a norm-one point for a nonnegative compactly supported continuous function.

## One place and three places

`normOneOne` is the identity twist `normOneAut K 1`, and `normOneOne_eq_id` identifies it with
`MonoidHom.id H`. `normOneFinitePlaceOrbital_one` specializes `normOneFinitePlaceOrbital` to
this twist: for one compatible choice of global measures, the orbital integral at `δ` of the
positive average of `x ↦ f_v(x_v) f^v(x)`, with `f^v` invariant under the points at `v`,
equals the local orbital integral of `f_v` at the component `δ_v` times a functional of `f^v`.

`LocalOrbitalNonvanishingAt v x t` says that the local orbital integral of `t` at `x` is
nonzero for some compatible local measures. `threePlaceTensor v₀ v₁ v₂ s₀ s₁ s₂ w` is the
function `x ↦ s₀(x_{v₀}) s₁(x_{v₁}) s₂(x_{v₂}) w(x)`.

`threePlaceTensor_orbitalIntegral_ne_zero` proves: let `v₀, v₁, v₂` be distinct finite
places, let the twisted centralizer of `δ` be commutative, let `w` be invariant under the
points at the three places, and let `t_i` have nonzero local orbital integrals at
`δ_{v_i}`. If the orbital integral of the positive average of
`threePlaceTensor b₀ b₁ b₂ w` is nonzero for every compatible choice of measures, then so is
that of `threePlaceTensor t₀ t₁ t₂ w`. The proof factors out one place at a time with
`normOneFinitePlaceOrbital_one`. At `v₀` the factorization shows that the functional of
`b₁ ⊗ b₂ ⊗ w` is nonzero, hence replacing `b₀` by `t₀` keeps the integral nonzero; the same
step at `v₁` and then at `v₂` replaces `b₁` and `b₂`. Between the steps the measures change,
and `twistedOrbitalIntegral_ne_zero_iff_of_isCompatible` transfers nonvanishing.

This is the factorization of global orbital integrals of factorizable functions into local
orbital integrals used in Arthur–Clozel, *Simple algebras, base change, and the advanced
theory of the trace formula* (1989), Chapter 1, proof of Lemma 6.5 (printed pp. 54–55).
