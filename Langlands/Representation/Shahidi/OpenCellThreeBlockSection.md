# Induction in stages for the block sizes `(1, d + 1, t + 1)`

Module `Langlands.Representation.Shahidi.OpenCellThreeBlockSection`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `threeReindex d t`: the reassociation `GL_((1 + (d+1)) + (t+1)) ≅ GL_(1 + ((d+1) + (t+1)))`,
  with its action on upper unipotents, torus elements and integral matrices.
- `leftSection ψ hϖ d t a₁ a' c D e₁`: the lift through the `(d+2, t+1)` parabolic of the
  degree-`D` piece of `δ^(1/2) F₁ ⊗ W°(·; c)`, where `F₁` is the lift through the `(1, d+1)`
  parabolic of the degree-`e₁` piece of `fullΦ a₁ a' 0`.
- `rightSection ψ hϖ d t a₁ a' c D e₁`: the lift through the `(1, d+t+2)` parabolic of the
  degree-`e₁` piece of `δ^(1/2) W°(·; a₁) ⊗ F₂`, where `F₂` is the lift through the `(d+1, t+1)`
  parabolic of the degree-`(D - e₁)` piece of `fullΦ a' c 0`.
- `threeBlockValue`: the common value at a three-block Levi point `(x₁, x₂, x₃)`:
  `[deg x₁ = e₁, deg x₂ = D - e₁] δ^(1/2) δ'^(1/2) W°(x₁; a₁) W°(x₂; a') W°(x₃; c)`.
The results below assume that `ψ` has conductor `𝒪`.

- `whittaker_mul_integral'`, `isLeviInvariant_leftSection`, `isLeviInvariant_rightSection`,
  `leftSection_mul_integral`, `rightSection_mul_integral`: right invariance under the integral
  groups.
- `leftSection_unipotent_mul_torus`, `rightSection_unipotent_mul_torus`: both sections at an
  upper triangular point are `threeBlockValue` at its three diagonal blocks; the moduli agree
  because `δ_(d+2,t+1) δ_(1,d+1) = δ_(1,d+t+2) δ_(d+1,t+1)` on the three-block Levi
  (`cpow_half_identity`).
- `leftSection_eq_rightSection`: `leftSection g = rightSection (threeReindex g)` for every `g`
  (Iwasawa decomposition and right invariance).

## Provenance

Transitivity of parabolic induction for `GL_n`, written explicitly for these sections.
