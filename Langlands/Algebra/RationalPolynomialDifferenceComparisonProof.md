# Polynomial coefficients from vanishing scalar differences

This proof of `RationalPolynomialDifferenceComparisonStatement` applies the published rational Newton construction
to the difference of two rational polynomial evaluation sequences. It assumes
that the indicated scalar difference vanishes after `d` forward differences.
It first proves equality of the scalar difference polynomial with the Newton
polynomial truncated in degree `d`. The next difference vanishes as well, so
the Newton evaluation formula and uniqueness from a natural-number tail give
this equality. The top Newton coefficient is zero, which identifies the
coefficients in degree `d`.

If the first polynomial is nonzero of exact degree `d` and the scalar is
nonzero, the difference polynomial has degree at most `d`, hence so does the
second polynomial. Its coefficient in degree `d` is nonzero by the coefficient
identity. Its degree is therefore exactly `d`, and the same identity is the
asserted leading-coefficient formula. All degrees include the case `d = 0`.
These are derived consequences of the published Newton reconstruction and
polynomial uniqueness lemmas, with no geometric input.
