# Integral action on a rank-one difference line

This internal algebra construction applies to a torsion-free abelian group
`M`, a nonzero element `a`, and an integer-linear automorphism `w`. Its
hypothesis is that every difference `x - w x` is an integral multiple of `a`.
The group and element have arbitrary universe `u`. No finite generation,
primitivity, root system, or finite-order hypothesis is needed.

`IntegralRootLine.lineUnit a ha w hdiv` is the actual unit of the integers
describing the action on `a`. Choose coefficients `m` and `n` in the difference
formula at `a` and at `w⁻¹ a`. These formulas give
`w a = (1 - m) • a` and `w⁻¹ a = (1 + n) • a`. Applying `w` to the second
equality and substituting the first shows
`((1 - m) * (1 + n)) • a = a`. Torsion-freeness and `a ≠ 0` allow cancellation,
so the two integer coefficients are inverses. This constructs `lineUnit`,
and `lineUnit_smul` proves its action formula.

The only integer units are `1` and `-1`. Consequently
`apply_eq_self_or_neg` proves `w a = a ∨ w a = -a`, and
`apply_eq_neg_of_ne` selects the negative sign when `w a ≠ a`.

These declarations are derived directly from the difference formulas and
Mathlib's integer-unit and torsion-free cancellation APIs. In the intended
relative-root application, `w` is the actual Weyl action on the character
lattice. The construction can turn movement of a root into the root-flip
hypothesis of integral coroot extraction. It assumes the automorphism and
integral differences are supplied; it constructs no rational normalizer
point and does not prove intrinsic relative-root reflection existence.
