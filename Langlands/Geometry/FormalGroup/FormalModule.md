# Formal O-modules in finite coordinates

`ModuleLaw O R σ` consists of a finite-coordinate commutative formal group
law over the commutative O-algebra `R`, a unital ring homomorphism from
`O` to its formal endomorphism ring, and the natural tangent condition.
Multiplication of endomorphisms is composition and their addition uses
the formal group law. Thus this is an action on actual formal series,
including the additive and multiplicative scalar identities.

The tangent condition is imposed on the degree-one coefficients:
the coefficient of the variable `j` in the output coordinate `i` of
`[a]` is `algebraMap O R a` when `j = i`, and is zero otherwise.
`CoordinateMap.linearCoeff` records this matrix, and `linearPart`
is the corresponding R-linear map on coordinate tangent vectors.
`action_on_tangent` proves that it is scalar multiplication by the
image of `a` for every tangent vector.

`M.Point κ` is the existing series-point additive group with an O-module
structure constructed by evaluating the formal endomorphisms `[a]`.
The module identities follow from the ring-action identities and from
additivity of evaluation. `map` extends coefficients along an O-algebra
homomorphism, preserving the tangent condition. `mapPoints` is the
resulting O-linear map. Over a coefficient algebra `A` in a scalar tower
`O → R → A`, `AlgebraPoint A` takes the base-changed points with no
formal variables. Its carrier is explicitly identified with the tuples
of nilpotent elements of `A`; its O-action is evaluated formal scalar
multiplication.

The original source is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), §1, opening Definition, printed p.108. It defines a formal
O-module over an O-algebra as a formal group with an O-action inducing
the natural tangent action. The Lean definition gives its chosen
finite-coordinate form and works for any commutative ring `O`, so it
applies in particular to the ring of integers in that definition.
The explicit matrices, ring packaging and point-module constructions
are derived implementation content. This module does not supply the
locally glued groups allowed in the final paragraph of §1, printed
p.109, or quasi-isogenies, heights or moduli representability.
