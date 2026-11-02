# Positive forms on actual finite-order determinant twists

This internal construction transfers a single positive definite Hermitian
form from an actual automorphic operator realization to its actual
finite-order determinant-multiplied image. The number-field universe is
arbitrary, coefficients are complex and the matrix rank is any natural
number. All represented functions and operators are the existing ones.

`HeckeCharacter.HasFiniteOrder.isUnitary` proves unit modulus on every
actual idele class. Evaluating the finite positive exponent relation gives
a complex root of unity; Mathlib's norm theorem gives modulus one. The
finite adelic and standard infinite compact determinant restrictions
inherit this same norm identity.

For a given actual whole-operator positive form `b`,
`OperatorRealization.UnitaryForm.determinantTwist` constructs a form on
the actual multiplied image. Its value on `f,g` is the original form on
their inverse determinant-multiplier images. The finite invariant form is
the published unit-modulus scalar twist of `b.finiteForm`, pulled through
the inverse of the published actual finite twist equivalence.

The compact construction applies the same procedure to `b.compactForm`
and the actual compact twist equivalence. Both have precisely the same
underlying form and multiplier, so the compact invariance identity applies
to the finite form already chosen. The published differential covariance
states that the actual enveloping action commutes with determinant
multiplication. A private linear-equivalence argument gives the inverse
covariance equation. Applying it in both arguments of the form reduces
the genuine real skew equation to the original `b.real_skew`.

`determinantTwist_inner` identifies the form in inverse multiplier
coordinates. `determinantTwist_inner_apply` states that determinant
multiplication preserves the chosen form exactly. The resulting
unitarizability witness descends to the existing whole-operator
isomorphism classes. Twisting that class by the inverse character and
using the published inverse-twist class identity proves reflection.
Thus actual whole-operator unitarizability is equivalent before and after
each finite-order determinant twist, both for actual representatives and
for their classes.

The provenance is internal: the actual multiplied subspace, multiplier,
finite and compact equivariances, differential covariance and inverse
class identity are existing constructions; generic invariant-form
twisting and Mathlib's complex norm result supply the remaining steps.
There is no compactness hypothesis on an additive adele quotient. This
does not construct a form when none is given, assert an invariant
integral formula, give a Hilbert globalization, prove spectral occurrence
or establish unitarity for an arbitrary nonunitary Hecke character.
