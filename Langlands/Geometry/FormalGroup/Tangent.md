# Tangent maps of finite-coordinate formal groups

The tangent map in chosen coordinates is the matrix of coefficients of
the degree-one monomials, acting on coordinate vectors. This module
proves the chain rule for that actual coefficient matrix and constructs
the induced tangent representation of an order action.

`CoordinateMap.coeff_subst_linear` states that the coefficient of a
linear monomial in a substituted series is the sum of the outer linear
coefficients times the inner linear coefficients. The substituted series
have zero constant coefficients, and the intermediate coordinate set is
finite. The proof truncates the substitution in total degrees less than
two, writes the degree-zero part as a constant and the degree-one part as
a sum of coordinate variables, and takes a linear coefficient. Thus no
higher-degree term contributes. `linearCoeff_comp` is the resulting
matrix product formula.

`linearPart_apply` expresses the tangent map as a finite matrix sum.
The tangent of the identity is the identity, the tangent of the zero map
is zero, pairing pairs tangent vectors, and `linearPart_comp` preserves
composition. For a commutative formal group law, `linearPart_addition`
proves that formal addition differentiates to ordinary vector addition.
Its proof differentiates the two formal identity equations, then splits
a vector in the sum coordinate space into its two components and uses
linearity. It does not assume the desired linear part as extra data.

`CommLaw.Hom.tangent` is the derivative of an actual formal group
homomorphism. It preserves addition and composition, and is bundled as
an additive homomorphism on Hom and a unital ring homomorphism on
endomorphisms. The addition proof applies the preceding result to the
formal definition of addition of homomorphisms. Inverse formal
homomorphisms yield inverse linear maps, giving `CommLaw.Iso.tangent`.

For formal O-modules, `ModuleLaw.Hom.tangentLinear` is O-linear in the
formal homomorphism; its target is the R-module of R-linear tangent
maps, with O acting through the coefficient algebra. Scalar
compatibility follows from the formal O-module's natural tangent
condition. `ModuleLaw.Hom.tangentEnd` preserves the endomorphism ring,
and `ModuleLaw.Iso.tangent` gives the corresponding R-linear
equivalence.

For a possibly noncommutative O-algebra A acting on a formal O-module,
`ModuleLaw.OrderAction.tangent` is a unital ring homomorphism
from A to the R-linear endomorphisms of the coordinate tangent space.
It is the composite of the actual formal action with differentiation.
`tangent_scalar` proves that its restriction along O to A is the natural
O-action on that vector space. `OrderAction.Hom.tangent_commutes`
proves that the derivatives of order-linear formal maps intertwine
these representations.

These constructions are derived infrastructure for the natural tangent
action in Drinfeld, *Coverings of p-adic symmetric regions* (1976), §1,
opening definition, printed p.108, and for the tangent-character condition
in §2 A, printed p.109. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The original passages were read directly. Drinfeld's local-field setting
specializes this algebraic construction, which only needs the displayed
commutative coefficient rings, finite coordinate sets and actual formal
actions. The module supplies coordinate tangent representations; the
special geometric-fibre condition, heights, locally glued formal groups
and moduli representability remain further work.
