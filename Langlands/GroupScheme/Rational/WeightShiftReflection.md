# Faithful tangent maps reflect adjoint weights

`representationTangentWeightSpace p r chi` is the intersection of the actual
tangent image of a representation with its weight-shifting endomorphisms
of degree `chi`.

`matrix_weightShift_comm` proves the all-algebra torus intertwining equation
for every weight-shifting endomorphism. It checks the two matrix actions
on each actual torus weight space, then uses their published spanning
property to obtain equality of linear maps. Evaluation on coordinate
vectors gives the matrix identity over the coefficient algebra.

For a monomorphic representation, its actual differential is injective
over every coefficient algebra. Applying that injectivity to the
intertwining equation proves that a weight-shifting tangent operator comes
from the actual adjoint weight space of the same degree. Together with the
forward implication, `kernelDifferential_mem_representationWeightShift_iff`
identifies actual adjoint weight with weight shift in a faithful
representation. No characteristic-zero or character-formula premise is
needed.

This is an internal derived helper for Task 7128's group-side Lie-weight
input to Freudenthal's formula.
