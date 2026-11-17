# Finite-dimensional regularization of a simple pole

This internal construction uses the algebraic coordinatewise analyticity from
`RealBlockMultiplierAnalytic` and scalar power-series calculus. It does not
equip an ambient representation space with a norm or topology.

`HasWeakDerivAt f v z₀` says that every algebraic complex linear functional
applied to `f` has derivative equal to its value on `v`. Algebraic dual
separation proves uniqueness. Addition and scalar multiplication preserve
this property.

A weakly analytic family lying in one finite-dimensional subspace has a
derivative vector in that subspace. Each coordinate functional of a finite
basis extends to the ambient vector space. The derivative vector is the sum
of the scalar coordinate derivatives times the basis vectors. Applying any
functional to this sum gives the derivative of its evaluation on the family.

For a family of linear maps with a derivative vector for every input,
`derivativeMap` chooses these unique vectors. Their uniqueness and the sum
and scalar rules prove that the result is a linear map. The construction
preserves any finite-dimensional subspace containing the corresponding
input's entire output family.

`removeSimplePole T h z` is `z⁻¹ • T z` away from zero and the derivative map
at zero. If `T 0 = 0` and each input's output family is weakly analytic at
zero, the quotient is weakly analytic there. On each scalar coordinate it is
the divided difference with its derivative value at the center; shifting the
scalar power series proves analyticity. The quotient retains the stated
finite-dimensional range bounds.

Two further tools support later applications. A pointwise weakly analytic
operator family sends a weakly analytic input family in one fixed finite
subspace to a weakly analytic family, by expansion in a finite basis.
Equality of two weakly analytic families on a nontrivial filter approaching
the parameter implies equality of their values there, by uniqueness of
scalar limits and algebraic dual separation.

The hypotheses concerning derivative vectors, analyticity, finite ranges
and a zero value remain explicit. This file does not prove that a particular
four-crossing family has those properties, construct an exceptional
intertwiner, or prove the full unlinked swap statement.
