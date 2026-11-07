# Mean value estimates along square-zero archimedean directions

Helper for the rapid-decay argument (`Langlands.Automorphic.CuspidalL2.Decay`).
Provenance: internal; it is the one-variable mean value inequality applied to a
smooth function on the archimedean group along a unipotent segment.

## Contents

- `ArchimedeanGL.squareZeroUnit Z hZ`: for an archimedean matrix `Z` with `Z * Z = 0`,
  the unit `1 + Z` with inverse `1 - Z`; `squareZeroUnit_val` gives its value.
- `ArchimedeanGL.smul_mul_smul_eq_zero`: `(s • Z) * (s • Z) = 0` whenever `Z * Z = 0`.
- `ArchimedeanGL.squareZeroElement Z hZ`: the infinite adelic element corresponding to
  `1 + Z` under `archimedeanGLCoordinates`.
- `ArchimedeanGL.norm_sub_le_of_squareZero f x Z hZ M hM` (**mean value estimate**): let
  `f` be a smooth function (`SmoothFunctions K n`), `x` an infinite adelic element and
  `Z` a real Lie algebra element whose matrix `Zm` satisfies `Zm * Zm = 0`. If
  `‖(smoothDifferential K n Z f).val (x * (1 + s Zm))‖ ≤ M` for all `s ∈ [0, 1]`, then
  `‖f.val (x * (1 + Zm)) - f.val x‖ ≤ M`.

  Proof: put `p s = x (1 + s Zm)` in matrix coordinates and `h s = F (p s)`, where `F` is
  the Library's `coordinateExtension` of `f`, differentiable at invertible matrices.
  The chain rule gives `h' s = dF_{p s}(x Zm)`. Because `Zm² = 0`,
  `x Zm = p s * Zm`, so `h' s` is the left-invariant derivative
  `(smoothDifferential K n Z f).val (x (1 + s Zm))`. The bound then follows from
  `norm_image_sub_le_of_norm_deriv_le_segment'` on `[0, 1]`.
