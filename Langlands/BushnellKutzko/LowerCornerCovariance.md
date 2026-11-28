# Covariance on a subgroup with a deeper lower corner

For orthogonal block projectors, `blockUnit e₁ e₂ h₂₁ y` is the unit
`g = 1 + w` with `w = e₁ y e₂`. `blockUnit_add` gives the addition law.
The identity `e₂ e₁ = 0` removes the quadratic term in the product.
`blockUnit_conj_lowerCorner` proves that `g k g⁻¹ − 1` and `k − 1` have
the same lower corner. In fact `e₂ g = e₂` and `g⁻¹ e₁ = e₁`.

If `β` commutes with `e₁`, then `w β w = 0` and
`g⁻¹ β g − β = βw − wβ`. The theorem `blockUnit_conjugationDifference`
records this identity. For a twist parameter `c ∈ P^(-m)` commuting
with both projectors, this adjoint expression is supported in the upper
corner of `P^(-m)` whenever `y ∈ P^0`. Cyclicity reduces its trace
against `k − 1` to a product with the lower corner of `k − 1`.
`blockUnit_elementCharacter_conj_eq` uses the BK additive-character
condition to kill this product when the lower corner lies in `P^(m+1)`.

`simpleHGroup_succ_eq_inf` identifies `H^(m+1)` with
`H^m ∩ U^(m+1)` for `m ≥ 1` by the carrier formula for the simple H
groups. `conjugationDifference_mem_traceDual_of_fixed` uses a BK additive
character and a simple character at index `m` on `H^(m+1)` within the
level and critical bounds. It assumes that `g` preserves that group by
conjugation and intertwines the character with itself. Intertwining
puts `g` in the double coset of BK93 (3.3.2). By (3.3.9), the
conjugation factor is the trace character of `g⁻¹ β g − β` against
`k − 1`. Every element of the domain lattice occurs as `k − 1`.
Cancelling the simple-character value proves that the difference
belongs to the trace dual of the domain lattice.

The source is Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), (3.3.2) and (3.3.9), printed pp. 105 and 108
(PDF pp. 117 and 120). The block formulas apply those identities to the
upper units used in (8.2.26).
