# Square-mean estimates along square-zero archimedean directions

Module: `Langlands.Automorphic.CuspidalAdmissible.SquareZeroL2`. Provenance: internal; the
square-mean companion of the Library's `ArchimedeanGL.norm_sub_le_of_squareZero`.

- `sq_lintegral_le μ hf`: for a probability measure, `(∫⁻ f)² ≤ ∫⁻ f²` (Hölder
  `ENNReal.lintegral_mul_le_Lp_mul_Lq` with exponents `2, 2` against the constant `1`).
- `continuous_squareZeroElement_smul`: `s ↦ 1 + sZ` is continuous into the archimedean group.
- `enorm_sub_sq_le_lintegral_squareZero f x Z hZ`: for a smooth function `f`, a point `x` and
  a real Lie algebra element `Z` with `Z² = 0` (as a matrix),
  `|f(x(1+Z)) - f(x)|² ≤ ∫_{[0,1]} |(D_Z f)(x(1+sZ))|² ds`. As in the Library, the curve
  `s ↦ f(x(1+sZ))` is differentiated through the coordinate extension of `f`; because
  `Z² = 0` the derivative is the left-invariant derivative `D_Z f` at `x(1+sZ)`. The
  fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, the
  derivative being continuous), `‖∫ g‖ ≤ ∫ ‖g‖` and `sq_lintegral_le` on `[0,1]` give the bound.
