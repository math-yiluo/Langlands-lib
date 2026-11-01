# Actual CM transport of whole-operator automorphic quotients

This internal construction applies the existing actual CM pullback to both
pieces of `OperatorSubquotient`: the numerator is its existing actual CM image,
and the denominator is its image under the proved invariant-subspace order
equivalence of the numerator actions. Thus `Q.complexConj` retains concrete
numerator and denominator data. The number field is an actual CM number field
in an arbitrary universe, the rank is any natural number, and coefficients
are complex.

`complexConj_lower_toSubmodule` identifies the denominator with the actual
linear image under `Q.upper.complexConjEquiv`. Mathlib's
`Submodule.Quotient.equiv` then induces `Q.complexConjEquiv` between the actual
module quotients. Its forward and inverse formulas on the canonical quotient
projections use precisely that numerator map and its inverse.
`complexConjEquiv_mem_lower_iff` reflects denominator membership, by the
projection's exact kernel and injectivity of the induced linear equivalence.
Complex values are fixed: the numerator map changes the adelic argument.

The whole-algebra covariance is proved by quotient induction, applying
the already proved numerator covariance to each representative and then
the transported canonical projection. Finite translation, standard infinite compact
translation and genuine enveloping differentials transform by the existing
CM finite, compact and enveloping maps. These identities are specializations
of the whole-algebra covariance through its proved generator formulas.

`complexConjRepresentationEquiv`, `complexConjFiniteEquiv` and
`complexConjCompactEquiv` give genuine representation equivalences from the
original actions precomposed with their actual CM parameter maps to the
actions on the transported quotient. Their linear map is the induced quotient
equivalence above. The finite and local restrictions retain the previously
proved smoothness of every actual `OperatorSubquotient`.

`complexConjSubrepresentationOrderIso` uses the published covariant image and
preimage construction on these quotient actions. Its simple-order criterion
preserves and reflects whole-operator irreducibility; it makes no assertion
that the finite restriction is irreducible.
`complexConjTwiceEquiv` composes the two actual quotient equivalences.
A private generic composition lemma combines the two whole-operator
covariance identities with involutivity of `cmOperatorConjugation`; this
proves that the composite is a genuine full-action equivalence with the
twice transported quotient. This does not identify dependent numerator/denominator
presentations by equality.

Provenance is internal: the existing actual CM image of a numerator,
its invariant-subspace covariance, Mathlib's induced module quotient
equivalence, and the previously constructed actual quotient representation.
No new identification with original literature is claimed. This unit supplies
no quotient function evaluation, quotient topology, local tensor-factor
selection, class descent, central-character or cusp predicate on arbitrary
quotients, or irreducible or spectral existence.
