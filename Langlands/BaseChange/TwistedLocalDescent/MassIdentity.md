# The mass identity for the twisted orbital kernel

Module `Langlands.BaseChange.TwistedLocalDescent.MassIdentity`, over an ultrametric proper
nontrivially normed field `𝕂`.

- `isOpenEmbedding_val_generalLinear`: `GL_n(𝕂) → M_n(𝕂)` is an open embedding.
- `integral_parabolic_congruence_eq`: for a compact congruence subgroup `U` of radius `r > 0`, a
  left Haar measure on `P`, an additive Haar measure `νS` on `𝔭` and a continuous compactly
  supported `φx` on `GL_n`,
  `∫_{P ∩ U} φx((1 + Z)⁻¹ d h θ(1 + Z)) dh =
  b · ∫_{W ∈ 𝔭, ‖W − 1‖ ≤ r} φ̃((1 + Z)⁻¹ d W σ(1 + Z)) dνS`,
  with `φ̃` the extension of `φx` by zero to `M_n` and `b` the constant of
  `map_val_restrict_parabolic_congruenceBall`.
- `integral_balls_eq_chart`: for continuous `σ`, a continuous bounded function `φt` on `M_n`
  (in the application `φ̃`, the extension by zero of `φx`), and assuming the change of variables
  `(ν|_{B(0,r)}).map χ = c • ν|_{A(B(0,r))}` for the chart `χ` at `d` (supplied in the mass
  identity by `map_restrict_closedBall_twistedChart`), the iterated integral over the balls of `𝔭`
  (about `1`) and `𝔲̄` (about `0`) of `φt((1 + Z)⁻¹ d W σ(1 + Z))` equals
  `c · ∫_{A(B(0,r))} φt(d (1 + Y)) dν(Y)`: Fubini, the translation `W = 1 + W'`,
  `blockSumMeasure_restrict_closedBall_zero`, the identity `mul_one_add_twistedChart` and the
  assumed change of variables.
- `integral_eq_chart_coordinates`: `∫_G φ = a · ∫_{A(B(0,r))} φ̃(d (1 + Y)) dν(Y)` for
  `φx = φ(x · θ(x)⁻¹)` continuous with compact support, `U` a compact congruence subgroup of
  radius `r`, and `a` the constant of `map_val_restrict_congruenceBall`. The support hypothesis
  is that `φx(y) ≠ 0` forces `y = d (1 + Y)` with `Y ∈ B(0, r) ∩ A(B(0, r))`. Proof: invariance of
  `μG` on both sides reduces `∫_G φ` to `∫ φx(d y) dy`; membership of `Y` in the original ball
  `B(0, r)` restricts this group integral to `U`; Haar measure on `U` in coordinates and
  translation to `0` turn it into `a` times an additive integral over `B(0, r)`; membership of `Y`
  in the image ball `A(B(0, r))` then restricts the additive integral to the chart image. (Support
  in `U` alone, i.e. in `B(0, r)` alone, would not suffice: the image ball can have smaller
  measure.)
- `integral_twistedOrbitalKernel_eq_mass` (**mass identity**): under the hypotheses of
  `integral_twistedOrbitalKernel_eq_iwahori` and of `MassChart` (rigidity, support, `δh`
  multiplicative and trivial on `P ∩ U`, `d (P ∩ U) ⊆ Q`), and if `A` is a continuous additive
  automorphism equal to the linear part of the chart at `d`, with `‖A⁻¹ Y‖ ≤ C ‖Y‖`,
  `ν.map A = c • ν` and `C · max(‖d⁻¹‖‖d‖, 1) · r < 1`, then

  `∫_K Φ = δh(d) · c · ∫_G φ`.

  The constants combine through `iwahoriConstant · b = a`.
