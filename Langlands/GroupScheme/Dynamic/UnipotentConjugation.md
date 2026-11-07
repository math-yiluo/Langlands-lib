# Conjugation on the contracting subgroup

Authors: Worker 1741 and Worker 1531 (interface and proof-route design).

For an affine group scheme over an affine base, a cocharacter `χ`, and a base
point `t` in its dynamic centralizer, `Affine.unipotentCommutator` is an actual
endomorphism of `Affine.unipotentScheme χ`. Its formula after the closed
inclusion into the original group is `v ↦ v t v⁻¹ t⁻¹`, on every test scheme.
The construction does not require a field, smoothness or finite type.

The universal point of the represented contracting subgroup belongs to its
all-test subgroup functor. Conjugating its inverse by the pullback of `t`
preserves that functor, because the dynamic centralizer lies in the dynamic
parabolic and the parabolic normalizes the contracting subgroup. Multiplying
by the universal point therefore gives another point of this same subgroup
functor. Its represented range property factors this actual scheme morphism
through the closed representative. Choosing that factorization defines the
endomorphism; restriction of the defining formula proves its all-test formula.

The theorem `exists_unipotent_conj_eq_mul` works over an algebraically closed
field. The original group is affine and locally of finite type. Suppose the
only point of the contracting subgroup commuting with `t` is the identity.
Then every `u` in that subgroup has a conjugator `v` in the same subgroup
satisfying `v t v⁻¹ = u t`.

Closed immersion into the original group makes the represented contracting
subgroup affine and locally of finite type. Equality of two commutator images
implies that the quotient of the two points commutes with `t`. The stated
centralizer condition makes that quotient the identity, proving injectivity
on rational points of the actual endomorphism. The internal affine-scheme
Ax–Grothendieck adapter gives surjectivity on those points. Lifting `u` through
the represented inclusion, choosing a commutator preimage and cancelling
`t⁻¹` yields the required conjugacy equation.

This unit is an internal consequence of the published all-test dynamic
representability and normalization results and Mathlib's Ax–Grothendieck
theorem through the internal affine-scheme adapter. It introduces no additional
external structure theorem or unproved premise. The theorem retains its
explicit commuting-point condition; it does not itself prove strongly regular
fibres of the class-function quotient.
