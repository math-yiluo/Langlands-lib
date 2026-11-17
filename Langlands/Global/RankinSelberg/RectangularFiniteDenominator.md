# A common finite denominator for rectangular coordinates

This internal module defines `rectangleFiniteCoordinates` by projecting
every rectangular adele entry to its finite part. It proves a global
finite-support consequence of the local bounds in
`AdelicRectangularRootBounds`.

Suppose a nonzero algebraic integer `q` makes every simple-root finite
coordinate integral. At each finite place its norm is at most one,
and every root has norm at most the reciprocal of its norm. Hence
`finiteSimpleRootRadius` is at most that reciprocal. The proof uses
the local norm characterization of the valuation ring and the
nonvanishing of the field embedding into the completion.

For an explicit standard-compact Iwasawa factorization of the
three-block rectangular chart, the local polynomial bound then gives
`‖x_ij,v‖ ≤ ‖q_v‖^(-d*(d+1))`. Thus `q^(d*(d+1))*x_ij` is integral
at every finite place. The final theorem states this as membership in
the actual `integralFiniteAdeles F`, with the same denominator for
every rectangular entry. The denominator depends on `q` and the
number of rectangular rows, and not on the leading block.

This theorem is a finite-coordinate estimate under the displayed
factorization and root-support hypotheses. It does not itself prove
archimedean decay or Mellin convergence.
