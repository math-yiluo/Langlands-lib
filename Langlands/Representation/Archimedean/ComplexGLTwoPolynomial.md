# Polynomial algebra for the irreducibility of `GL_2(ℂ)` principal series

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoPolynomial` (namespace
`Langlands.Archimedean.GLTwoPoly`). It serves the proof of
`ComplexGLTwoUnlinkedIrreducibleStatement` (module `ComplexGLTwoUnlinkedIrreducibleProof`).

Provenance: internal infrastructure with no literature source. It is the polynomial side of the
classical computation of the `U(2)`-types of principal series of `GL_2(ℂ)`. Functions of the bottom
row `r` of `g ∈ GL_2(ℂ)` are written as polynomials in `r` and `r̄`.

## Definitions

* `Var = Fin 2 ⊕ Fin 2`, `Pol = MvPolynomial Var ℂ`; `z k = X (inl k)` stands for `r_k`,
  `w k = X (inr k)` for `r̄_k`; `N = z₀w₀ + z₁w₁` (that is, `|r|²`).
* `dz k`, `dw k`: the partial derivatives `∂/∂z_k`, `∂/∂w_k` (`pderiv`).
* `EZ = z₀∂_{z₀} + z₁∂_{z₁}` and `EW = w₀∂_{w₀} + w₁∂_{w₁}` (Euler operators);
  `Lap = ∂_{z₀}∂_{w₀} + ∂_{z₁}∂_{w₁}`; `D i k = z_i ∂_{z_k} - w_k ∂_{w_i}`.
* `Eig a b` (`a b : ℂ`): the joint eigenspace `EZ P = a P`, `EW P = b P`. For natural `a`, `b` it is
  the space of polynomials of bidegree `(a, b)` (`mem_Eig_iff_coeff`).
* `Cas P = 2 D₀₁(D₁₀ P) + 2 D₁₀(D₀₁ P) + (D₀₀ - D₁₁)²P`, twice the Casimir operator of `𝔰𝔩_2` in
  the operators `D i k`, and `casValue a b = 2a(a+1) + 2b(b+1) - (a-b)²`.
* `holMove s i k h = s z_i w_k h + N z_i ∂_{z_k} h`.
* `ev r P = P(r, r̄)`; `toReal`, `fromReal`: the substitutions `z ↦ x + iy`, `w ↦ x - iy` and back.
* `Two u v m`, `mono u v m t = X u^{m-t} X v^t`, `raise u v = X u ∂_v`, `lower u v = X v ∂_u`:
  polynomials of degree `m` in two variables, with raising and lowering operators.

## Main results

* Leibniz and commutation rules: `pderiv_comm`, `EZ_dz` (`EZ ∘ ∂_{z_k} = ∂_{z_k} ∘ EZ - ∂_{z_k}`) and
  the other commutators, `Lap_z_mul`, `Lap_w_mul`, `Lap_N_mul`.
  Consequently `Eig` is preserved or shifted by `z_k ·`, `w_k ·`, `N ·`, `∂`, `Lap`, `D i k`
  (`z_mul_mem`, …, `D_mem`, `holMove_mem`).
* `Cas_eq`: on `Eig a b`, `Cas P = casValue a b · P - 4 N Lap P`.
* `Lap_Lap_holMove`: for `h ∈ Eig a b` with `Lap h = 0`,
  `Lap (Lap (holMove s i k h)) = 2(s + a + b + 1) ∂_{z_k}∂_{w_i} h`.
* `exists_traceless_ne_zero`: if `h ∈ Eig a b`, `Lap h = 0`, `a b ≠ 0` and `h ≠ 0`, then one of
  `∂_{z₁}∂_{w₀}h`, `∂_{z₀}∂_{w₁}h`, `∂_{z₀}∂_{w₀}h - ∂_{z₁}∂_{w₁}h` is nonzero.
* `mem_span_zw`: polynomials of bidegree `(a+1, b+1)` are combinations of `z_k (w_i R)` with `R`
  of bidegree `(a, b)`.
* `eq_zero_of_ev`: a polynomial with `P(r, r̄) = 0` for all `r ≠ 0` is zero.
* `Eig_le_of_stable_left`, `Eig_le_of_stable_right`: a nonzero subspace of `Eig m 0` (or `Eig 0 m`)
  stable under `D 0 1` and `D 1 0` is all of it.

## Proofs

The identities follow from the Leibniz rule (`pderiv_mul`), the commutation of partial derivatives
(`pderiv_comm`, by `MvPolynomial.induction_on`) and the Euler relations of `Eig a b`. These are
combined with `ring` and `linear_combination`. `Cas_eq` writes `Cas` as `2Σ_{ik} D_ik D_ki - (D₀₀+D₁₁)²`
(since `(D₀₀ - D₁₁)² = 2(D₀₀² + D₁₁²) - (D₀₀+D₁₁)²`), uses `D₀₀ P + D₁₁ P = (a - b) P` on `Eig a b`,
and expands `D i k (D k i P)` (`D_D`). `Lap_Lap_holMove` uses `Lap(z_i Y) = ∂_{w_i}Y + z_i Lap Y`,
`Lap(w_k Y) = ∂_{z_k}Y + w_k Lap Y` and `Lap(N Y) = (2 + a + b)Y + N Lap Y` on `Eig a b`. The
coefficient description of `Eig` (`coeff_EZ`, `coeff_EW`) gives `Eig a b = 0` when `a` or `b` is not a
natural number. This yields `mem_span_zw` (factor `z_k w_i` out of each monomial). It also yields
the two-variable description of the bottom types (`Eig_le_Two_left/right`). `eq_zero_of_ev`
substitutes `z = x + iy`, `w = x - iy` (inverted by `fromReal`) and applies
`MvPolynomial.funext_set` on the nonzero real points. `Two_le` applies `raise^τ` to a nonzero
element, with `τ` the largest index of a nonzero coefficient, which gives `X u^m`. It then applies
`lower^t` to reach every monomial (`raise_pow_mono`, `lower_pow_mono` use `Nat.descFactorial`).
