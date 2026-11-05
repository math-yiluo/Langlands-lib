# A positive-characteristic torus power

`TorusPowerPoint G x p` records an actual commutative torus, its closed inclusion
into `G`, an actual rational point of that torus, and an index `r : ℕ` with
`x ^ (p ^ r) = rationalPoints.map inclusion point`.

For a smooth connected affine commutative group scheme over any field
`k : Type u` of prime characteristic `p`, `positiveCharacteristicTorusPower`
constructs these data for every actual rational point `x`. No perfectness or
algebraic-closedness assumption is imposed. Since `p` is prime, its exponent
`p ^ r` is positive, including when `r = 0`.

The implementation is a derived application of the published arbitrary-field
nilpotent central-torus and unipotent-exponent results. First,
`isNilpotentGroupScheme_of_isCommMonObj` transports commutativity through the
actual base-change functor to the algebraic closure; its group of geometric
points is abelian and hence nilpotent. The constructor then takes
`IsNilpotentGroupScheme.centralTorusQuotient`, retaining its smooth connected
affine quotient. `IsNilpotentGroupScheme.isUnipotent_of_no_torus` proves that
quotient unipotent from the supplied absence of torus images. The
`exists_hasUniformPowerExponent_of_isUnipotent` theorem supplies `p ^ r`
killing the quotient on all tests.

Applied to the image of `x`, this exponent puts `x ^ (p ^ r)` in the actual
scheme kernel of the quotient. The fppf quotient's all-test kernel equality
identifies that kernel with the range of the torus inclusion. Membership on the
original rational test therefore supplies an actual rational torus point with
the required image equation. This argument uses no surjectivity of the quotient
on rational points: it uses the represented kernel equality. The constructor
records only the torus, its closed inclusion and point, not a splitting of the
original extension or a factorization for characteristic zero.
