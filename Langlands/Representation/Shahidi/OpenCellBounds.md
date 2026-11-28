# Elementary bounds for Schur functions and half moduli

Module `Langlands.Representation.Shahidi.OpenCellBounds`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `norm_det_le_of_le`: if every entry of an `m × m` complex matrix has norm at most `x`, its
  determinant has norm at most `m! x^m`; `norm_multiset_map_prod_le`: a product of `k` factors of
  norm at most `M ≥ 0` has norm at most `M^k`.
- `norm_eval_hsymm_le`: for `x ∈ ℂ^m` with `‖x_i‖ ≤ M` (`M ≥ 0`), the complete homogeneous
  symmetric polynomial of degree `k` satisfies `‖h_k(x)‖ ≤ 2^(m+k) M^k`;
  `norm_eval_completeSymm_le`: for `x ∈ ℂ^m` with `‖x_i‖ ≤ M`, `M ≥ 1`, and an integer degree
  `k ≤ K` (the polynomial being `0` in negative degree), `‖h_k(x)‖ ≤ 2^(m+K) M^K`.
- `norm_satakeSchur_le`: for `x ∈ (ℂˣ)^(n+1)` with `‖x_i‖ ≤ M`, `M ≥ 1`, and an antitone
  `λ ∈ ℤ^(n+1)` with `λ_(n+1) ≥ 0` and `∑ λ_i = D`, the Library's Schur function
  `satakeSchur x λ` (Jacobi–Trudi determinant) satisfies
  `‖s_λ(x)‖ ≤ (n+1)! · (2^(2(n+1)) M^(n+1))^(n+1) · (2^(n+1) M^(2(n+1)))^D`.
- `norm_halfModulus_le`: for `q ≥ 1` and `λ ∈ ℤ^(n+1)` with `∑ |λ_i| ≤ D`, the half modulus
  satisfies `‖δ_B^(1/2)(ϖ^λ)‖ ≤ q^(n D)`.
- `sphericalWhittaker_unipotent_mul_torus`: for an integrally trivial character `θ`, an upper
  unipotent `u` and an antitone `λ`, Shintani's formula gives the value
  `θ(u) δ_B^(1/2)(ϖ^λ) s_λ(x)` of the Library's `sphericalWhittaker` at `u ϖ^λ`;
  `..._of_not_antitone`: the value is `0` when `λ` is not antitone (no hypothesis on `θ`).
- `norm_sphericalWhittaker_le_of_nonneg`: for an integrally trivial unitary `θ`, `q ≥ 1`,
  `‖x_i‖ ≤ M` with `M ≥ 1`, and `λ ≥ 0` with `∑ λ_i = D`, the value at `u ϖ^λ` has norm at most
  `q^(n D)` times the bound of `norm_satakeSchur_le`; `norm_sphericalWhittaker_le_of_nonpos`: the
  same bound for `λ ≤ 0` with `∑ λ_i = -D` under `‖x_i⁻¹‖ ≤ M`, using
  `Conductor.satakeSchur_inv` (`s_μ(c) = s_(-w₀μ)(c⁻¹)`).

## Provenance

Elementary estimates used for the uniform half-plane of
`Langlands.Shahidi.UnramifiedOpenCellSumStatement`; Shintani's formula is the definition of
`GeneralLinear.Spherical.sphericalWhittaker` (Shintani 1976,
`shintani-1976-class-one-whittaker`, p. 181).
