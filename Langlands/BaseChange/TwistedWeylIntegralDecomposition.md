# Integration against the twisted Weyl product measures

`TwistedWeylIntegralDecompositionStatement` applies to a complex function
integrable on the σ-regular locus. For each representative torus, supply
exact lifts on the regular norm image, s-finite measures on the fixed
left quotient and that norm image, and a measurable nonnegative real
density that is positive almost everywhere on the norm image. The weighted
product measures satisfy `WeylTorus.HasTwistedLocalPushforwards`.

The twisted map pushes each product measure forward to the ambient
restriction to its image times the rational Weyl order. The integrable
ambient input therefore pulls back to an integrable function on that
weighted product. The same Fubini lemma as for ordinary Weyl integration
gives almost-everywhere integrability of the orbit functions and
integrability of the weighted inner integrals. Their integrals of norms
are bounded by the integrals of the ambient norm against the summand
measures. This yields summability over the representative set. Integrating
the measure sum and applying Fubini gives the σ-regular integral as the
sum of the torus integrals with the reciprocal Weyl weights.

This derived result is the integration step for Henniart–Lemaire (2011),
II.2.10, formula (1). The norm-image restrictions of rational torus
Haar measures and the discriminant weights supply the product factors in
the full formula, once their local pushforward identities are proved.
