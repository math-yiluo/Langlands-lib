# Ordinary cup normalization and naturality

Authors: Worker 45 (proof draft); Worker 211 (author audit and submission documentation).

`Langlands.Tate.ordinaryCupLaws : Langlands.Tate.OrdinaryCupLaws.{u}` proves the
normalization and coefficient naturality specification in the published module
`Langlands.Cohomology.Tate.OrdinaryCupStatement`. This is an internal, derived proof
using the published explicit ordinary cup and Mathlib's cohomology interfaces.
The target statement and all imported construction dependencies are unchanged.

`ordinaryClass_invariant` identifies the cohomology class of the cocycle obtained
from an invariant vector with its image under the inverse of Mathlib's `H0Iso`.
It uses the compatibility of the cocycle projection with `H0Iso`, then cancels
the isomorphism. `ordinaryCup_zero_invariant` applies the actual cup's
representative certificate to these cocycles. Evaluating their empty tuples
reduces the result to the coefficient pairing on invariant vectors.

`iCocycles_coefficientMap` expresses the actual cocycle map as coefficient
postcomposition after inclusion in cochains, using `cyclesMap_i`.
`ordinaryCupCocycles_naturality` applies this identity and the explicit tuple
formula for the cup. The coefficient-level intertwining hypothesis moves the
output map through the pairing, and equivariance of the second input map moves
it through the ordered prefix action. Extensionality of cocycle inclusions
then gives the equality of cocycles.

`ordinaryCup_naturality` represents arbitrary cohomology classes by cocycles,
using surjectivity of Mathlib's class projections. The actual cup representative
certificate and the class-map compatibility reduce its assertion to the
preceding cocycle identity. Finally, `ordinaryCupLaws` packages exactly the two
clauses of the target proposition.

All constructions use actual Mathlib ordinary group cohomology. The proof works
in arbitrary common universe u over every commutative ring and group, without
finiteness or flatness hypotheses. Its checks use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. No tensor-boundary law or
ordinary-to-Tate cup comparison is proved here.
