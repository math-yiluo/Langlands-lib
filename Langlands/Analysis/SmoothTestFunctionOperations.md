# Pullback and differentiation on complex test functions

These constructions supply the continuous operations on the test space
used in Shalika (1974), §2. Pullback by a real continuous linear equivalence
takes a fixed compact support to its inverse image. The iterated derivative
is obtained by composing in each direction with that equivalence, so the
derivative seminorm bounds pass to the pullback.

Differentiation along a smooth real vector field evaluates the real Fréchet
derivative at the field. It preserves support and is complex-linear in the
test function. On each fixed compact space, continuity follows from
Mathlib's derivative and pointwise bilinear application operators. The
universal property of the test-function topology gives continuity of both
constructions.
