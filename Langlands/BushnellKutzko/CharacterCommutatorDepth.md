# Adjoint congruence subgroups and the trace of a commutator

`mixedAdjointUnitGroup` is the group of units whose difference from one
belongs to an ambient filtration step and whose commutator with the
parameter has the mixed depth. Positivity of the ambient depth gives
membership in the corresponding unit filtration. The adjoint is a
derivation, and the commutator with the inverse unit is the negative of
the original commutator multiplied by the inverse on each side. Both
inverse factors lie in the order. This proves closure and gives the
bound for the difference between the conjugated parameter and the
original parameter.

`commutatorElement_sub_one` gives the ring expansion of the difference
from one of a group commutator. For congruence depths `k` and `l`, the
conjugation difference on the second input has depth `k + l`.
Replacing that difference by the group commutator minus one introduces
one more factor of depth `l` and an inverse factor in the order.
`elementCharacter_commutator_of_depth` uses `r + 1 ≤ k + 2 l` to place
this error, after multiplication by a parameter of depth at least
`−r`, in the depth-one lattice. Its trace lies in the conductor ideal.
Cycling the products in the trace identifies the remaining value with
the element character of the conjugation difference of the parameter.

The source is Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), source ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`,
(1.4.3) and (1.4.10), printed pp. 36 and 38, and (3.2.6)–(3.2.9),
printed pp. 100–102 (PDF pp. 112–114). In the mixed form the underlying
lattice is `mixedAdjointLattice`. For a pure parameter it equals the
relative lattice product via the fractional inverse identity.
