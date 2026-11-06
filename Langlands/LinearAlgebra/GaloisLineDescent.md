# Fixed bases of semilinear Galois lines

This internal algebraic construction considers a finite field extension `L/k`,
a subgroup `H` of its actual `k`-automorphisms, and an `L`-vector space `V`
in an independent universe. The action on `V` is additive and semilinear
with respect to the ordinary coefficient action of `H` on `L`.

The subgroup is the full automorphism group over its fixed field, by the
published Mathlib subgroup/fixed-field equivalence. Transporting a unit-valued
cocycle across this equivalence lets Mathlib's Hilbert 90 theorem give a
unit `d` with `sigma(d) / d = c(sigma)`. This step does not require that
`L/k` itself be Galois.

When `V` has dimension one, choose any initial linear basis vector `v`.
Write `sigma(v) = c(sigma) v`. Every coefficient is nonzero, and the action
law and semilinearity give
`c(sigma tau) = sigma(c(tau)) c(sigma)`. The preceding Hilbert 90 result
then shows that `d^-1 v` is nonzero and fixed by all of `H`.
Multiplication of that vector by scalars is a linear equivalence `L -> V`
intertwining the given action with the ordinary field action.
The noncomputable definition `equivariantLinearEquiv` chooses such an
equivalence, and `equivariantLinearEquiv_smul` proves its intertwining law.

This is a derived algebraic prerequisite for stabilizer-compatible root-line
coordinates. It does not assert that an actual root line has dimension one,
identify the restriction fiber with one orbit, or identify a relative root
group with a restriction of scalars. It supplies no R1 existence theorem,
global compatibility, valuation, or apartment witness.
