# Scalar extension of cochain insertion identities

This internal helper extracts the algebraic scalar-extension argument used in
the actual automorphic compact cochain differentiation construction. It allows
the same argument to be reused for genuine coefficient and tensor actions.
It adds no topological structure or group differentiation assumption.
`Automorphic/CochainCompactDifferentiation` reuses these public helpers
for its original automorphic cochain argument.

`complexMultilinear_ext_on_real` proves that complex multilinear maps on the
actual complexified archimedean Lie algebra agree if they agree on all tuples
from the real Lie algebra. The proof curries one argument, uses tensor
induction in it, and proceeds by induction on the number of arguments.

`complexCochainInsertion` is the actual finite sum inserting a fixed linear
endomorphism into each argument of an alternating cochain.
`complexCochainInsertion_of_real` applies the extensionality result to prove
that an insertion identity on real tuples holds on every complex tuple.
Its real-tuple premise must still be proved by the intended application.
Degree zero is included, with the empty insertion sum.
