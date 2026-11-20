# Elliptic Cartan comparison from support and evaluation

`separatedRegularCoordinates` requires distinct logarithmic radii across the complex and real
slots together and requires a nonzero sine in each complex slot. For each complex and real slot
pair, inequality of their radii is open. In any open neighborhood of a coordinate tuple, one can
vary just the chosen complex radius by a continuous update and avoid the chosen real radius.
The finite intersection of these open dense sets, intersected with `regularCoordinates`, is dense.
Here the angle and sign coordinates are fixed by the update. The nonzero set of the continuous
numerator is open and is nonempty for positive induced weights by
`exists_regular_numerator_ne_zero`. It therefore meets `separatedRegularCoordinates`.

`RealStandardEllipticCartanEvaluationStatement` is an internal premise for comparing the actual
real standard modules. It asks for scalar evaluations on the separated regular coordinates of
Cartans with total rank `2 * r + s`. It requires invariance under the target's bijective compact
and Lie intertwiners. An evaluation vanishes when a list has fewer than `r` induced blocks. For
exactly `r` induced blocks and `s` real characters, the evaluation equals the finite numerator
times a nonzero factor depending only on the Cartan coordinates and slot counts. Both formula
clauses take a permutation witness for the enumeration and positive weights in its induced slots.

The Lean proof of `realStandardEllipticCartanComparison_of_evaluation` enumerates each list by
collecting its two types of blocks and then replacing the two lists by `Fin`-indexed data. A
permutation preserves membership and rank, so the enumerated weights are positive and the rank of
each list is twice its induced count plus its character count. All evaluations and the intertwiner
invariance use the original lists. If one induced count were larger, the formula at that count
would yield a nonzero evaluation for its list and the support clause would give zero for the other
list at the same point. Intertwiner invariance excludes both strict inequalities. The common total
rank then forces the character counts to agree. On that common Cartan, cancellation of the nonzero
factor gives equality of the numerators on the separated regular coordinates, and continuity
extends equality to all coordinates. The comparison keeps the target's irreducibility hypotheses
and the evaluation premise uses only the rank and intertwining hypotheses for invariance.

These are consequences of the finite numerator theory and the stated evaluation premise. The
support and evaluation of the actual modules are the representation-theoretic input to this
conditional reduction.
