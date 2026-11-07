# Cyclic Frobenius in degree coordinates

This internal construction continues the algebraic degree-coordinate equivalence.
It retains arbitrary groups, a coefficient field, and independent universes.
The degree scaling is written as `n + 1`, so the positive length is explicit.

`cyclicOperator` transports the actual action of the ambient degree-one element
on degree-kernel invariants of Mathlib's coinduced representation through
`InductionDegree.coordinates`. Its value on coordinate zero is the source
degree-one action applied to the last coordinate; its value on coordinate
`i.succ` is the previous coordinate `i.castSucc`. These are precisely the
coordinate conditions of `LocalFactor.EulerCyclicBlockStatement`.

The implementation proves the two formulas first for the coordinate image of
an actual invariant function. Right translation by the ambient element raises
the argument's degree by one. At a successor coordinate this gives the previous
negative power. At coordinate zero, the same degree is represented by the
source degree-one element followed by the last negative power. Equal-degree
values agree, and source equivariance supplies the wraparound action.
Conjugating by the coordinate equivalence then gives both formulas for every
coordinate vector.

This is a derived algebraic helper for the Euler-factor induction proof. It
does not assert a determinant identity or specialize to local Weil groups.
