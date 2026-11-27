# Restriction of the twisted orbital kernel to `d (P ∩ K(r))`

Module `Langlands.BaseChange.TwistedLocalDescent.MassChart`.

## Extension by zero

`continuous_extend_zero_of_isOpenEmbedding`: extending a compactly supported continuous function
by zero along an open embedding into a Hausdorff space gives a continuous function;
`extend_zero_apply_of_injective`, `exists_eq_of_extend_zero_ne`. Used to view a test function on
`GL_n` as a continuous function on `M_n`.

## Support and rigidity

Over an ultrametric, proper, nontrivially normed field, let `θ` be the entrywise action of a
ring endomorphism `σ`, `d ∈ P`, `U` a congruence subgroup of radius
`r`, `A` the linear part of the twisted chart at `d` with `χ(B(0,r)) = A(B(0,r))`, and suppose
(`hsupp`) that every `y` with `φ(x y θ(x)⁻¹) ≠ 0` has matrix `d (1 + Y)` with `Y ∈ A(B(0,r))` and
`‖Y‖ ≤ r`.

- `exists_twistedConj_of_support`: such `y` are `(1 + Z)⁻¹ d h θ(1 + Z)` with `‖Z‖ ≤ r`,
  `h ∈ P ∩ U` (`exists_twistedConj_of_mem_chart`).
- `lowerUnit_mem_congruence`: `1 + Z ∈ U` for `‖Z‖ ≤ r`.
- `rel_of_twistedOrbitalKernel_ne_zero`: under the rigidity hypothesis (`hrig`: a twisted
  conjugator from an element of `Q` to an element of `d (P ∩ U)` lies in `P`), every `k` with
  `Φ(k) ≠ 0` lies in `P U x⁻¹` (the hypothesis of the β-identity).
- `twistedOrbitalKernel_lowerUnit_mul_inv`: if moreover `δh` is multiplicative and trivial on
  `P ∩ U`, and `d (P ∩ U) ⊆ Q`, then

  `Φ((1 + Z) x⁻¹) = δh(d) ∫_{P ∩ U} φ(x (1 + Z)⁻¹ d h θ(1 + Z) θ(x)⁻¹) dh`.

  Only `p ∈ d (P ∩ U)` contribute: if `p ∈ Q` and the integrand is nonzero, `(1 + Z)⁻¹ p θ(1 + Z)`
  is `(1 + Z')⁻¹ d h' θ(1 + Z')`; rigidity puts `(1 + Z')(1 + Z)⁻¹` in `P`, so `Z' = Z`
  (`lowerUnit_eq_of_mul_inv_mem`) and `p = d h'`. Left invariance of `μP` under `d` finishes.
