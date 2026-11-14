# Numbered integral coordinate vectors of type D

This internal coordinate calculation defines the simple vectors in the order
`e_0-e_1, ..., e_(n-2)-e_(n-1), e_(n-2)+e_(n-1)` for `n ≥ 2`.
The forward coordinate differences telescope into the simple-vector monoid.
For `a < b`, the sum `e_a+e_b` is the last simple vector plus
`e_a-e_(n-2)` and `e_b-e_(n-1)`. Reordering gives the result for any distinct
indices. Consequently every signed pair is in that monoid or its negative is.
Coordinate sum and initial-coordinate sums are computed explicitly.

These are elementary deductions from the displayed coordinate formulas and
introduce no external classification assertion. The module does not yet
construct a numbered root-datum base or a group-scheme cover.
