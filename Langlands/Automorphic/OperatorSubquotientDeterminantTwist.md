# Actual determinant twists of whole-operator automorphic quotients

This internal construction applies the published finite-order determinant
multiplier to the actual numerator and invariant denominator of an
`OperatorSubquotient`. The number field has arbitrary universe, the rank is
any natural number and coefficients are complex. The input character has
explicit finite order, as required by the existing analytic preservation
construction on automorphic functions.

`Q.determinantTwist` uses the existing actual multiplied numerator and maps
its denominator through the proved numerator invariant-subspace order
equivalence. Its denominator is exactly the linear image under the actual
numerator multiplier. `determinantTwistEquiv` is Mathlib's induced module
quotient equivalence for that image equality. The forward and inverse
projection formulas describe its action on representatives. The exact
projection kernel and injectivity of this equivalence prove that denominator
membership is preserved and reflected.

Quotient induction carries the proved numerator covariance through the
canonical target projection. The result retains every element of the
concrete automorphic operator algebra. The finite and standard infinite
compact identities have the same determinant-character scalar as on the
numerator; the projection's complex linearity moves that scalar outside.
The genuine enveloping differential action commutes with the quotient map
without a scalar. These identities construct a genuine equivalence with the
whole-action pullback and genuine equivalences from the existing finite and
compact scalar twists to the actual quotient actions. The transported object
is itself an `OperatorSubquotient`, so its finite and whole-carrier local
restrictions retain the existing smoothness proofs.

The published covariant invariant-subspace construction, applied to the
actual quotient equivalence and concrete determinant operator automorphism,
identifies all whole-action invariant subspaces. Its simple-order criterion
preserves and reflects whole-action irreducibility, including nontriviality.
It makes no irreducibility assertion for the finite restriction.

`determinantTwistInvEquiv` composes the actual quotient maps for the character
and its inverse. A private generic composition argument applies both
covariance identities and cancels the algebra automorphism with its inverse.
The existing determinant-conjugation inverse formula supplies precisely that
inverse. This gives a canonical genuine whole-action equivalence from the
original quotient to the twice-twisted quotient, with the exact composite
application formula. No equality of dependent quotient presentations is
required.

Provenance is internal: actual numerator determinant images and their proved
covariance, Mathlib's module quotient equivalence, the existing scalar-twist
construction and the published invariant-subspace order equivalence. This
follows the actual quotient image route of `OperatorSubquotientCMTransport`
with determinant multiplication instead of CM argument pullback. It claims
no new identification with original literature. No quotient evaluation or
topology, class descent or character action law, selected tensor factor,
central-character or cusp predicate on arbitrary quotients, or nonzero,
irreducible or spectral existence is asserted.
