# Unitary twists and analytic coefficients modulo the full center

Author: Worker 429.

The theorem `Langlands.unitaryTwistModCenter` proves the closed proposition
`Langlands.UnitaryTwistModCenterStatement.{uG,uV}`, with independent group and
complex-module universes. It preserves and reflects square-integrability and
temperedness for the same supplied Haar measure on the full central quotient.

`UnitaryCentralCharacter.unitaryTwist` multiplies the actual scalar central
character by the restriction of `χ` to the full center. The intersection of the
two open kernels is contained in the product character's kernel, so that kernel
is open. Norm multiplicativity proves norm one. The scalar action follows
from the original central action and associativity of scalar multiplication.

`coefficientNorm_unitaryTwist` compares the two functions on the actual central
quotient by quotient induction. At a representative, linearity pulls `χ(g)`
out of the functional; its norm one proves equality of coefficient norms.
This helper applies to every algebraic functional, without a smoothness premise.

The square-integrability and temperedness preservation lemmas transport
admissibility using `isAdmissible_twist_iff` and use the newly constructed
central-character datum. For each smooth functional on the twisted
representation, `smoothContragredientTwistEquiv` supplies the same underlying
functional in the original smooth dual. The coefficient functions coincide,
so the existing `MemLp` proof applies to the same measure and exponent. The
temperedness lemma retains every vector and every real positive epsilon.

The closing theorem uses these preservation lemmas for the inverse character.
Its kernel equals the original kernel and its values again have norm one.
`twist_inv_twist` identifies the double twist with the original representation,
giving both reflection implications. The two preservation implications then
complete the conjunction.

All arguments are internal consequences of unchanged Library definitions and
published twist transport results. No Haar uniqueness, inversion invariance,
contragredient integrability, reductive-group theorem, classification,
continuation or Jacquet multiplicity theorem is used. The group and module
universes remain independent, and the result concerns every supplied Borel Haar
measure on the full central quotient with no additional carrier or group
restrictions.
