# Coefficient models under the minus-one diagonal

This supporting module constructs the standard-to-inverse and
inverse-to-standard functional translations at a fixed additive character.
Both use the published character-change diagonal at `-1` and then retype the
covariance character using the published character identities. Translation
in either direction twice is the identity; nonzero functionals remain nonzero.

Every coefficient-model vector is translated by left multiplication by this
diagonal. The maps onto the translated coefficient models are surjective:
write a vector as a coefficient of its functional and keep the same underlying
representation vector. Since the diagonal commutes with `-I`, this translation
preserves any supplied model minus-one scalar.

These are internal derived constructions supporting the direct fixed-character
JPSS factor exchange proof. They make no claim that inverse-transpose models
are smooth contragredients, and assume no analytic or factor-existence result.
The functional-equation transport is implemented in `EqualRankSwapEquations`.
