# Norm of the finite divisor of an actual idele

Worker 1692 derives these internal comparisons from `HeckeDivisor`,
`IdeleAbsoluteValue` and Mathlib's normalized completion norms. The field has
unrestricted universe `u`. The constructions use the existing idele divisor,
the actual inclusion of finite ideles, and the existing normalized absolute
value.

`finiteDivisor x` is the divisor of the finite idele included in the full idele
group with infinite component one. It preserves multiplication as addition of
divisors. For each completion unit, the local norm is
`N(v) ^ (-ord_v(x))`, with exactly the local order used by the Hecke shell
formulas. The proof writes the normalized completion norm in terms of its
valuation and substitutes the valuation exponent comparison.

The divisor norm is strictly positive. Its finite support product also equals
the unordered finite product over all places: a place outside the divisor's
support contributes the zeroth power, one. The local norm comparison then gives
`norm (ideleDivisor x) = (∏ᶠ v, ‖x_v‖)⁻¹`.

Consequently the divisor norm of a finite idele is the inverse of the existing
finite idelic absolute value. For a full idele the existing absolute value is
the product of its archimedean norms, with the original place multiplicities,
times the inverse of its divisor norm. The inverse occurs because the divisor
order is positive on a uniformizer, whose normalized local absolute value is
`N(v)⁻¹`.

These are arithmetic comparisons; no class representative decomposition,
adelic integral identity, analytic continuation or functional equation is
claimed.
