# Addition of actual tangent maps at a monoid identity

This is an internal construction for an arbitrary field `k`, in an arbitrary
universe. It proves the compatibility between addition of actual point-stalk
derivations and multiplication of actual dual-number points of a monoid scheme.
It requires no smoothness, commutativity, finite type or representability theorem.

The double test is the spectrum of `DualNumber (DualNumber k)`, with its actual
structure morphism to `Spec k`. Write a ring element as
`((a,b),(c,d)) = a + b e₁ + c e₂ + d e₁e₂`. The first and second inclusions of
`DualNumber k` specify the two projections of the test. The two axis morphisms
are spectra of setting the other parameter to zero. The diagonal is the
spectrum of the algebra homomorphism `fold`, which sends this element to
`(a,b+c)`. The implementation checks that this formula preserves multiplication;
the mixed coefficient maps to zero because epsilon squared is zero.

`DualNumberDouble.doubleIsLocalRing` proves locality by detecting units with the
projection to the first dual-number ring. The diagonal followed by either
projection is the identity. An axis followed by its matching projection is also
the identity; its other projection factors through the actual closed-point
augmentation and the actual structure map.

`fold_comp_eq_lift` is the coefficient calculation: if a ring map to the double
dual-number ring restricts on the two axes to the augmented lifts of derivations
`D` and `E`, its composite with `fold` is the augmented lift of `D+E`. This uses
the constant coefficient from the first axis and the infinitesimal coefficients
from both axes.

`tangent_diagonal_eq_add` proves the corresponding equality of actual scheme
maps for any rational point of any scheme over `k`. A map from the double test
with the prescribed axes sends the closed point to the specified rational
point. The canonical map from the spectrum of that point's actual stalk
therefore factors the given map, by `Scheme.stalkClosedPointTo`. Canceling the
canonical stalk map, which is a monomorphism, identifies the two ring-map
restrictions with the lifts of `D` and `E`. The coefficient calculation then
gives the desired diagonal map.

`rationalStalkDerivationPoint` packages the already constructed actual tangent
map as a morphism in `Over (Spec k)`. Its augmentation is the specified section.
For a monoid object `P` in that slice, `rationalStalkDerivationPoint_add` states
that at the identity section this construction takes `D+E` to the product of
the points associated to `D` and `E`. The proof pulls the two points back along
the double test's two projections and multiplies them. The unit laws give its
two axis restrictions, the diagonal gives their product, and
`tangent_diagonal_eq_add` identifies this with the sum derivation.

The provenance is internal: the construction follows directly from the actual
dual-number algebra, the published rational-stalk tangent equivalence, Mathlib's
canonical local-stalk factorization, and the Yoneda monoid laws. This module
supplies an operation formula. It does not assert the final field-linear Picard
tangent/H1 equivalence, and it leaves its parameter classification and scalar
compatibility to the subsequent comparison.
