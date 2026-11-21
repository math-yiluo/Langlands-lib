# Integration against the ordinary Weyl product measures

`OrdinaryWeylIntegralDecompositionStatement` applies to an integrable function on
the regular semisimple locus. Each representative torus has an s-finite coset
measure, an s-finite measure on its regular point set, and a measurable
nonnegative real density that is positive almost everywhere. The
product measure weighted in the torus coordinate satisfies
`WeylTorus.HasOrdinaryLocalPushforwards`.

The measure decomposition expresses the ambient restriction to the regular
locus as a sum of pushforwards scaled by reciprocal rational Weyl orders.
On each torus image the unscaled pushforward is a finite multiple of the
ambient restriction. Pullback therefore gives integrability against the
weighted product. Fubini applied to the density times the pulled-back
function establishes integrability of the orbit function for almost every
torus point, since the weight is positive almost everywhere. The integral
of the norm of the weighted inner integral is bounded by the integral of
the norm against the corresponding summand measure. Summing this bound
gives summability of the torus integrals of norms. Integrating the measure
sum and applying Fubini gives the common integral.

This derived step implements the integration of the ordinary Weyl measure
decomposition used by Henniart–Lemaire (2011), II.2.10, formula (2). In that
application the weights come from the ordinary discriminant and the
measures come from the Haar measures and their compatible quotient
measures. The statement takes the weighted local pushforward identities
as premises.
