# Heights along torus elements and the key inequality

Module: `Langlands.Global.SiegelFiniteness.Heights` (namespace
`Langlands.Global.SiegelFiniteness`). Provenance: internal; a step of the implemented proof of
`SiegelSetGLFinitenessStatement`, using the Library's normalized height of primitive adelic
vectors (`PrimitiveAdelicHeight.height`, maximum coordinate norms at all places, archimedean
multiplicities retained).

Notation: `A_x = ofInfinite (torInf x)` is the archimedean torus element `diag(e^{x_i})`,
`d = [F : ℚ]`, `e_j = Pi.single j 1`.

- `isPrimitive_rational_single`, `height_rational_single`: the rational basis vectors are
  primitive of height `1` (all local maximum norms are `1`).
- `height_single_le`: for a primitive vector `y` and an index `t` such that the vector
  `Pi.single t (y t)` is primitive, its height is at most that of `y` (local comparison
  `height_le_of_local_le` with constant `1`).
- `realScale_exp_eq`, `torus_mulVec_apply`: `A_x` multiplies the `i`-th coordinate by
  `realScale (e^{x_i})`, the value of the positive real idele `full (expUnit x_i)`.
- `exp_le_height_torus` (**lower bound**): if `v` is rational and `v_t ≠ 0`, then
  `e^{d x_t} ≤ H(A_x v)`. The `t`-th coordinate of `A_x v` is the idele value
  `full(expUnit x_t) · v_t`, whose normalized absolute value is `e^{d x_t}` (product formula
  `full_diagonalUnits` for `v_t`); compare with `height_single_le`.
- `height_torus_single`: `H(A_x e_j) = e^{d x_j}` (`IsPrimitive.height_smul`).
- `ofInfinite_torInf_inv`: `A_x⁻¹ = A_{-x}`.
- `exists_key_bound` (**key inequality**): for `n > 0` and a compact set `Q` of `GL_n(𝔸)` there
  is `β` such that whenever `γ A_x q = A_{x'} q'` with `q, q' ∈ Q` and the `(t, j)` entry of
  `γ⁻¹` is nonzero, `x'_j ≤ x_t + β`. Proof: with the uniform distortion bound `B` for `Q⁻¹`
  (`exists_pos_isHeightDistortionBound_of_isCompact`), the vector
  `(A_{x'} q')⁻¹ e_j = q⁻¹ A_{-x} w`, `w = γ⁻¹ e_j` (`rational_mulVec`), has height at most
  `B e^{-d x'_j}` and at least `B⁻¹ e^{-d x_t}` (since `w_t ≠ 0`); take logarithms:
  `β = 2 log B / d`.
