# Nonzero normalized infinite Whittaker residuals

For the finite presentation and additive support from the factorization
setting, `exists_infiniteResidual_ne_zero` shows that the normalized
infinite residual of every nonzero infinite tensor has a nonzero value on
`unipotentIntegralOutside`. The finite reference vector at each place of
`S` has value one under the supplied functional.

The global vector formed from the prescribed finite and infinite tensors is
nonzero because each normalized finite reference is nonzero, tensoring
nonzero vectors over `ℂ` preserves nonzeroness, and the tensor comparison is
injective. The global Whittaker expansion supplies a nonzero value of that
vector's Whittaker function.

There are only finitely many nonintegral local coordinates of the point at
which that value occurs. At a finite place outside `S`, multiply the point on
the right by the inverse of its local component embedded at that place.
The original Whittaker value is the value at the resulting point times the
spherical local factor, by the published unramified factorization theorem.
Thus the value stays nonzero after removing that coordinate. Induction over
the finite set of nonintegral coordinates gives a point integral outside
`S`.

The adelic group decomposition then expresses this point as the retained
infinite and `S` components followed by one combined integral factor away
from `S`. That factor fixes the actual global vector. At the retained
point, finite separation expresses the still nonzero value as a finite
product times the normalized infinite residual. This proves the required
nonzero residual value. The argument applies to the inverse character
using the published finite additive support theorem for that character.

This internal argument uses the Library's global Whittaker expansion,
unramified factorization, and tensor realization. Its conclusion concerns
one residual function and one point. The subsequent infinite-place
separation also needs comparisons of local Whittaker maps.
