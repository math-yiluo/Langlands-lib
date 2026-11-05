# Integral exponent weights over an arbitrary ring

For an affine locally finite type group scheme `G` over `Spec R` and an
actual homomorphism from a split torus with finite coordinate index `I`,
this file constructs an internal direct-sum decomposition of the actual
Lie module `Additive (lieKernel G R)`. It uses integral exponents `I → ℤ`
as indices. The base ring is arbitrary, including disconnected,
nonreduced and nonnoetherian rings. The torus homomorphism need not be
injective.

`exponentWeightSpace` imposes the adjoint weight equation for every
commutative test algebra `A` and every point of the actual split torus
over `A`. The character value in this equation is the actual exponent
monomial. This definition does not assume a decomposition or a
finite-dimensional representation.

The proof uses the published `universalAdjointCoefficients`, whose
coefficients satisfy the all-test weight equation and sum to the
original Lie vector. The universal-point monomial computation is
proved over arbitrary rings. Evaluating the weight equation at that
universal point shows that the coefficient family of a weight vector
is concentrated at its own exponent.
`Langlands.LinearAlgebra.finsuppDecomposition` then supplies
`exponentAdjointDecomposition`. The maps `exponentProjection` are the
actual coefficient projections and retract the inclusions of their
weight spaces. Thus every weight space is an actual direct summand.

Over a field, `exponentWeightSpace_eq_weightSpace` identifies these
spaces with the Library's existing all-test character weight spaces
using `characterLatticeEquiv`. Integral exponents are used before this
field specialization because characters of a split torus over a
disconnected ring may have different exponents on different
components; a global field-style character-lattice identification is
not assumed.

The provenance is internal: the construction extends the implemented
universal-coefficient proof of the published field weight decomposition,
using the already ring-general coefficient and adjoint operations. It
is an input to the relative adjoint-weight argument in Conrad,
*Reductive group schemes* (2014), Proposition 3.1.9(1), pp.85–88.
This file alone proves neither local finite freeness nor constancy of
fibre dimensions, extension of a fibre torus, or openness of the
reductive locus.
