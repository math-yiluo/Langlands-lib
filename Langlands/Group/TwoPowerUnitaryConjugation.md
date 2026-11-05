# Internal unitarization of elements of two-power order

This internal construction by Worker 1655 concerns polynomially defined
matrix subgroups over an arbitrary-universe `RCLike` field. The subgroup
is assumed stable under conjugate transpose. It constructs conjugating
elements inside that subgroup. It does not assert existence of such a
realization for an arbitrary reductive group.

## A unitary square

`exists_positive_conjugator_of_square_unitary` starts with an element
`g` whose square is unitary. The published internal polar construction
writes `g = k a`, where `k` is unitary and `a` is positive definite,
with both factors in the subgroup.

Unitarity of `g²` gives
`g g* = (g* g)⁻¹`. Substitution of the polar factorization yields
`k a² k⁻¹ = a⁻²`. Both `k a k⁻¹` and `a⁻¹` are positive definite.
Uniqueness of positive square roots therefore gives
`k a k⁻¹ = a⁻¹`.

Take an internal positive square root `c` of `a`, using the published
positive-power theorem for polynomially defined subgroups. The same
positive-square-root uniqueness argument gives
`k c k⁻¹ = c⁻¹`. Consequently `c g c⁻¹ = k`, which is unitary.
The square-root uniqueness used here is the continuous-functional-calculus
uniqueness theorem on matrices with their positive-semidefinite order.

## Induction on the exponent

`exists_conjugator_of_two_power_unitary` proves that if `g^(2^r)`
is unitary, some element of the subgroup conjugates `g` to a unitary
element. At exponent zero, use the identity conjugator. At the next
exponent, first apply induction to `g²`. Conjugate `g` by the resulting
element, so its square is unitary, and apply the preceding construction.
The product of the two conjugators stays in the subgroup.

`exists_conjugator_of_two_power_eq_one` specializes this to elements
whose `2^r`th power is the identity.
Its conclusion is `HasInternalUnitaryConjugate H g`, the proposition
that there exists `c ∈ H` with `c g c⁻¹` unitary.

The provenance is the implemented polar-factor and positive-square-root
argument. No compact-subgroup conjugacy theorem is assumed. These results
provide an internal conjugation tool for cocharacter evaluations at roots
of unity; a cocharacter comparison and existence of a compatible
realization remain separate obligations of the archimedean Iwasawa task.
