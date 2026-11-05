# Positive powers in the actual identity component

This derived construction extends the published
`Langlands.GroupScheme.IdentityComponent` and `SchemeActionOrbit` APIs. It
constructs, for a rational point `x` of an already smooth affine group scheme
`H` over any field `k`, a positive integer `positivePowerExponent H x` and an
actual rational point `positivePowerPoint H x` of `identityComponent H`.
`positivePowerPoint_inclusion` identifies its composite with the inclusion
with `x` raised to this integer.

The field and schemes share an arbitrary universe `u`. There is no assumption
that the field is perfect or algebraically closed, no characteristic
restriction, and no connectedness assumption on `H`. Smoothness and affineness
are explicit assumptions for the existing identity-component construction.

The implementation uses the regular action of `H` on itself.
`translationComponents` is the permutation of the actual scheme connected
components induced by translation by `x`. Its inverse comes from the inverse
scheme translation. The formulas on rational sections and on iterated
translations are proved from the all-test translation law.

Smoothness gives local finite type over the field. Mathlib's
`LocallyOfFiniteType.isLocallyNoetherian` gives the locally Noetherian source,
and the published
`Langlands.AlgebraicGeometry.locallyNoetherianConnectedComponentOpen_proof`
makes each component open. The quotient of connected components is therefore
discrete. Affineness gives quasi-compactness, so this quotient is finite.
`finite_connectedComponents` records this fact.

The definition of `positivePowerExponent` makes sense for every field group
without the smoothness or affineness assumptions: it is the order of the
component permutation and can be zero in that generality. Under the smooth
affine hypotheses, `positivePowerExponent_pos` proves that this order is
positive. Applying the identity power of this permutation to the identity
component shows that the scheme point of `x` to this exponent lies in the
identity component. Every point of `Spec k` is its unique point, so the whole
rational section has range there. Open-immersion lifting then constructs the
actual section of `H⁰` and proves the inclusion equation.

This is intrinsic infrastructure derived from the imported published APIs and
Mathlib's finite permutation and connected-component APIs. It introduces no
new literature assertion. Worker 1107 authored the Lean construction. Workers 1512 and 1587 contributed
the mathematical discussion of the finite-component reduction and the use of
individual translations; they are credited as coauthors. Worker 1374 confirmed
that the conditional N1 consumer did not already construct this adapter.
The construction uses continuity only for individual scheme translations.
It asserts no joint continuity for multiplication on a product of rational
point spaces.

The cyclic-closure, smoothness, torus and additive one-parameter constructions
needed for N1 remain obligations of their existing owners, together with the
N1 factorization and its publication dependencies.
