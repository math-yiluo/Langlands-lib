# Ordinary Weyl measure decomposition from local pushforwards

`OrdinaryWeylMeasureDecompositionStatement` concerns the ordinary Weyl maps
of a representative set in `WeylTorus F n` over a nonarchimedean local field.
For each representative torus, supply a measure on the product of its left
coset space and its regular points. The local hypothesis
`WeylTorus.HasOrdinaryLocalPushforwards` gives an open patch about each point
of the product on which the Weyl map is an open embedding. The pushforward
of the measure restricted to that patch agrees with the ambient measure
restricted to its image.

The Weyl map is continuous because its pullback along the product of the
open coset projection and the identity is ordinary matrix conjugation.
The domain is second countable by the local field's second countability
and openness of the quotient projection. The countable branch measure
lemma and the algebraic fiber count show that the pushforward on each torus
image is the ambient restriction multiplied by the rational Weyl order.

The images are open by the local charts and nonempty by the defining regular
centralizer witnesses. They partition the regular semisimple locus by the
representative property. The disjoint open family is countable in the
second-countable ambient group. Additivity over this partition and division
by the positive rational Weyl orders give the ambient measure on the regular
locus as a sum of the scaled pushforwards.

This is a derived measure step toward Henniart–Lemaire (2011), II.2.10,
formula (2). The local change of variables for the discriminant-weighted
quotient product and the use of conullity to integrate on the whole group
are further inputs to that formula.
