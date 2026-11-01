# All integral Rosati equations from finite coordinates

This internal consequence concerns the same actual positive Harris order and
its existing integer basis as `HarrisIntegralRosatiCompatibility`. The
arithmetic types are universe zero and the scheme universe is independent.
All tensor, Picard, dual evaluation and dual geometry data remain explicit.

`IntegralRosatiEquations` requires the actual equality
`a(x) ≫ λ = λ ≫ dual(a(τ(x)))` for every element of the integral order.
Here `a` is a supplied unital integral endomorphism action, `λ` is a supplied
actual homomorphism to the constructed dual abelian scheme, and `τ` is the
restriction of the existing positive auxiliary left involution.

`integralRosatiEquations_iff_basis` identifies this condition with the earlier
`IntegralRosatiBasisEquations`. In the forward direction one specializes to
basis vectors. For the converse, actual dualization is integer linear by the
explicit `DualSchemeMapAdditivity` premise, the involution is integer linear,
and composition with a fixed homomorphism is integer linear in a preadditive
category. Thus both sides define integer linear maps from the order to the
actual Hom group. Equality on its integer basis proves equality everywhere.
This argument uses no rationalization or injectivity of the actual Hom group
into rational Hom.

`IntegralRosatiTupleEquations` writes these finite equations directly in a
tuple `r` already satisfying the finite unit and ordered multiplication
equations. If `c_jk` is the integer coefficient of `b_j` in `τ(b_k)`, its
Rosati equation is `r_k ≫ λ = λ ≫ dual(∑ j, c_jk • r_j)`.
`integralRosatiEquations_reconstruct_iff` proves that the reconstructed actual
integral action satisfies every order equation exactly when these explicit
finite tuple equations hold. The proof combines the integer-basis criterion
with the existing reconstruction formula and its basis-value identity.

The provenance is internal integer linear algebra applied to published actual
dualization and composition. These results do not assert existence of an
integral action, a polarization, a moduli scheme or a representing locus, and
do not infer actual equalities from rational ones.
