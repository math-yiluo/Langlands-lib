# A value on a prescribed pure quaternion line from real local isotropy

Let `F` be a number field and `D` a central quaternion division algebra over `F` with
canonical conjugation `τ`. Let `H` be an invertible antihermitian `I × I` Gram matrix with
`3 ≤ card I`. Let `w ≠ 0` be a pure quaternion, `τ w = -w`, with `w² = c ∈ F`.

`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.exists_value_on_pureLine_of_real`
assumes one local condition: at every real place `v` where `c` is a square in `F_v`, there is a
nonzero row `y` over `F_v ⊗ D` with `∑ y_j (1 ⊗ H_jk) τ(y_k) = 0`. The conclusion is a global
row `x` and a nonzero `b ∈ F` with `τ.sesqForm H x x = b • w`. No condition is imposed at the
finite places, at the complex places, or at the real places where `c` is negative.

## The component theorem

`Langlands.GroupScheme.KneserThree.QuatData.exists_vector_on_pureLine_of_real` gives a
nonzero `x` with `τ.sesqForm H x x ∈ F · x_Q`, for quaternion coordinates `Q` whose
distinguished pure quaternion is `x_Q`, under the same local hypothesis on `Q.c`. The proof
applies Hasse–Minkowski
(`numberFieldQuadraticIsotropy_of_cyclicNorm` with `cyclicHasseNorm`) to the symmetric
component `C` of the skew form over `E = F(x_Q)`. This is a nondegenerate quadratic form of
dimension `2 · card I ≥ 6` over `E`. Its local isotropy is checked place by place.

- At a finite place of `E`, `localQuadraticAnisotropicDimensionBound` bounds anisotropic
  forms by dimension four.
- A complex completion has characteristic zero and every element is a square
  (`complexCompletion_isSquare`). A quadratic form of dimension at least two is then isotropic
  (`quadraticForm_not_anisotropic_of_forall_isSquare`).
- At a real place `w` of `E` over `v`, the root of `E` maps to some `θ` with `θ² = c`. If `c`
  were not a square at `v`, then `-c = s²` there. Mapping `s` to the completion at `w` would
  make `θ² + s² = 0` in a real completion, so `θ = 0`. This contradicts `θ ≠ 0`. So `c` is a
  square at `v`. The hypothesis gives an isotropic row, which `exists_isotropic_tensor_of_row`
  turns into a nonzero isotropic tensor. The map of completions keeps it nonzero (flatness)
  and isotropic. `exists_isotropic_component_of_isotropic` then gives an isotropic vector of
  the component.

A global isotropic vector of `C` has its skew value on the line `F · x_Q`
(`symmetricComponent_self_eq_zero_iff`).

## The nonzero coefficient

If the coefficient is zero, the form is isotropic over `F`.
`exists_sesqForm_eq_of_isotropic` shows that then every alternating element is a value. A
nondegenerate pairing gives `z` with `B(x, z) = 1`, after scaling by `τ(B(x, z)⁻¹)`. Then
`B(βx + z, βx + z) = β - τβ + B(z, z)`, and `β = (w - B(z, z)) / 2` gives the value `w`.

This implements the projective representation argument of T. A. Springer's appendix to
M. Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), Proposition 5.3.2,
printed p. 109 (PDF p. 115). Its local hypothesis is weakened to isotropy at the real places
where `w` is not elliptic. The weakening uses the dimension of the symmetric component.
