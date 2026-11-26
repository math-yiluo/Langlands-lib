# Equivalence of cusp-form realizations of equivalent Hilbert summands

`Langlands.Automorphic.GroupSchemeFunctions.generalLinearCuspidalSummandEquivalence`
proves `GeneralLinearCuspidalSummandEquivalenceStatement`. It uses the given
linear isometry between summands of the full almost-everywhere cuspidal space of
`GL_{r+1}` and the two given dense realizations by cusp forms on the
positive-central rational quotient.

Let `jP` and `jQ` be the two maps that send forms to their `L²` classes, with
codomains restricted to the respective summands. They have dense range by the
closure hypotheses. The quotient Haar measure has full support, so
`generalLinearFormClass_form_eq` identifies continuous forms with the same class.
This gives injectivity of each map. The class map commutes with finite adelic and
standard archimedean compact translations by the corresponding quotient class
identities.

For either summand, pull back its inner product along the class map. The finite
and compact actions preserve the pulled-back positive form because the bounded
right action preserves the `L²` inner product. The cusp-form realization is jointly
admissible by `CuspidalOperatorRealization.isJointlyAdmissible`. The dense image
comparison `jointVectorRecovery_of_dense` now identifies the class image with the
vectors which are smooth for the finite adelic action and finite for the standard
archimedean compact action. Here finite adelic smoothness means that the vector
has an open stabilizer, and compact finiteness means that its compact orbit spans a
finite-dimensional space. The isometry preserves both conditions in both directions
because it is an injective intertwiner of the two actions. Thus `U` carries the
range of `jP` onto the range of `jQ`. The two injective maps and this range equality
supply a linear equivalence `L` with `jQ (L f) = U (jP f)`.

Injectivity of `jQ` and equivariance of the class maps show that `L` commutes with
finite and compact translations. For a real Lie algebra element `X`, the theorem
`generalLinearCuspidalFormClassDerivative` identifies the derivative along
`exp(t X)` at zero with the class of the Lie action of `X`. The inclusion of a
summand has the subspace topology, so the difference quotients converge to this
class in the summand. By equivariance and continuity, `U` maps the difference
quotients for `jP f` to those for `jQ (L f)`. Uniqueness of their limit and
injectivity of `jQ` show that `L` commutes with the real Lie action.
`envelopingAction_comm_of_lieAction` extends this to the complex enveloping
algebra, and `OperatorRealization.Equivalence.ofGenerators` combines the three
intertwining identities.

## Provenance

The argument implements the direction from unitary equivalence to equivalence of
forms in Getz–Hahn, *An Introduction to Automorphic Representations* (Springer
GTM 300, 2024), Theorem 6.6.4, p. 172 (PDF p. 186). The joint-vector comparison
realizes the passage to the finite part of the discrete cuspidal representation
in Theorem 6.6.2, pp. 170–171 (PDF pp. 184–185), and in Theorem 9.7.3 and (9.40),
pp. 265–266 (PDF pp. 277–278). The statement supplies the dense class maps.
The registered source is `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
