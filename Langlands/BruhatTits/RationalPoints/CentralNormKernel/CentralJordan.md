# Jordan decomposition of central rational points

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement`. Let `K` be a field, `G` a group scheme over
`Spec K`, `ρ : MatrixRepresentation G N` and `D : SpectralData K (CentralAlgebra ρ)`. For a
central rational point `z` (proof `hz`):

- `isUnit_centralElement`: the element of the central algebra given by `z` is a unit (inverse
  from `z⁻¹`).
- `blockEigenvalues D hz i = χ i (ρ z)` as units, and `semisimpleMatrix D hz` is the
  block-scalar matrix `diagHom` of these units (module `Laurent`). `semisimpleMatrix_val`: it is
  the matrix of `D.semisimplePart (ρ z)`; `semisimpleMatrix_mem`: it lies in the central algebra;
  `semisimpleMatrix_mul_apply`: entries of `s g` are `∑ i, λ i (E i g)_{kl}`.
- `unipotentMatrix D hz = s⁻¹ ρ(z)`, with `commute_semisimpleMatrix`,
  `semisimpleMatrix_mul_unipotentMatrix` (`s u = ρ(z)`), `commute_unipotentMatrix`, and
  `isNilpotent_unipotentMatrix_sub_one`: `u - 1 = s⁻¹ (ρ(z) - s)` is nilpotent, as a commuting
  product with `ρ(z) - s`, the image of `x - semisimplePart x`.

Closure (with `coordMap` from module `PointLifting`):

- `classify_semisimpleMatrix_eq_zero_of_charP` (`CharP K p`, `p` prime): `classify s` kills
  `RingHom.ker (coordMap ρ)`. If `N` is empty all matrices agree. Otherwise
  `(u - 1) ^ k = 0` for some `k`, and with `q = p ^ k ≥ k`,
  `u ^ q - 1 = (u - 1) ^ q = 0` (`sub_pow_char_pow_of_commute` in the matrix ring, which has
  characteristic `p`). Since `s` and `u` commute, `ρ(z ^ (q k')) = s ^ (q k')`, which is
  `diagHom ((λ ^ q) ^ k')`; matrices of rational points kill the kernel, and
  `classify_diagHom_eq_zero_of_pow` applies, with `x ↦ x ^ q` injective (`iterateFrobenius`).
- `classify_semisimpleMatrix_eq_zero_of_charZero` (`CharZero K`): the same conclusion from
  `ρ(z ^ k) = diagHom (λ ^ k) * u ^ k` and `classify_diagHom_eq_zero_of_unipotent`.
- `mem_center_of_rationalMatrix_mem`: if `ρ` is a monomorphism, a rational point whose matrix
  lies in the central algebra is central (`commute_scalarMap_of_mem` and injectivity of
  `ρ.pointMatrix`).
- `exists_central_unipotent_decomposition` (`G.X.left` affine, `ρ` a closed immersion): there is
  a central rational point `u` with `ρ(u) - 1` nilpotent and `ρ(z) = s ρ(u)`. By the closure
  results (characteristic zero or prime, `CharP.exists'`) and the lifting theorem
  `exists_rationalMatrix_eq`, `s = ρ(g)` for a rational point `g`, which is central by the
  previous item; take `u = g⁻¹ z`, whose matrix is `s⁻¹ ρ(z)`.
