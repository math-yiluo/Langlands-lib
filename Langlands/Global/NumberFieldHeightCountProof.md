# Polynomial height count over a number field

`Langlands.Global.numberFieldMulHeightCount` proves the published
`Langlands.Global.NumberFieldMulHeightCountStatement`. For each number field
`K` the proof gives a constant depending on `K` and an exponent `2d + 1`, where
`d` is the cardinality of the index type of the integral basis of `K`.

For `B ≥ 1`, an element `x` of height at most `B` has positive canonical
denominator `n = Algebra.natDenominator x` with `n ≤ B`, by Mathlib's
`NumberField.natDenominator_le_mulHeight₁`. Each archimedean absolute value of
`x` is at most its height, since all factors in the height product are at least
one. The mixed embedding of the algebraic integer `n x` therefore has norm at
most `B²`. The continuous real coordinate map for
`mixedEmbedding.latticeBasis K` sends this embedding to the integral basis
coefficients. Each coefficient has absolute value at most `A B²`, where `A`
is the maximum of one and the operator norm of the coordinate map.

The map sending `x` to `n - 1` and the coefficient tuple is injective since
the nonzero denominator and the numerator recover `x`. The denominator has at
most `⌊B⌋` choices and each coefficient has at most `(2A + 1) B²` choices.
The resulting cardinality bound is `(2A + 1)^d B^(2d + 1)`.

This internal proof implements the elementary denominator and integral lattice
argument described in the published statement's Markdown. It uses Mathlib's
number-field height product and denominator estimates and its real lattice
basis for the mixed embedding.
