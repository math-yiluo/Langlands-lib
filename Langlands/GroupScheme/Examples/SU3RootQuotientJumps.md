# Quadratic root-coordinate jumps modulo the central subgroup

Worker 244. This is an internal derivation from the published quadratic
coordinate group, its literal zero-first-coordinate subgroup, and the optimal
trace-one representative lemmas in `SU3RootQuotientDepth`.

`quotientJumpValues` consists of the real thresholds at which the closed
`depthA` ball is not contained in the product of the strict ball and the actual
central subgroup. `centralJumpValues` uses closed and strict `depthDouble` balls
in that central subgroup itself. These are definitions on the supplied
coordinate group and valuation.

Two coordinate points differ by right multiplication by a central point if and
only if their first coordinates agree: their quotient has first coordinate
zero. Every central point belongs to the product of a strict ball with the
central subgroup, since the identity has infinite depth. For a nonzero first
coordinate and a supplied maximal trace-one scalar `t`, strict membership modulo
the central subgroup is equivalent to strict membership of the optimal lift.
One direction uses maximality of its depth; the other uses equality of first
coordinates to supply the central correction.

Assume the valuation is invariant under the involution and that `t` has trace
one and maximal valuation among trace-one scalars. The quotient jump thresholds
are exactly the real `r` for which some nonzero `x` satisfies
`ω x + halfTop (ω t) = r`. Noncontainment supplies a point whose optimal depth
is at least `r` and cannot exceed `r`; conversely the optimal lift at exactly
`r` supplies a noncontainment witness. Central jumps are exactly the finite
depths attained by nonidentity central points, by the same closed-versus-strict
comparison. These equivalences require no discreteness or characteristic
hypothesis. Existence of the maximal trace-one scalar is an explicit premise of
the quotient characterization.

This module does not identify an arbitrary actual root group with these
coordinates or prove the host apartment theorem. Those comparisons and the
arithmetic separation of root jumps remain separate obligations.
