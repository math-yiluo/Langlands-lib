# Twisted Weyl measure decomposition from local pushforwards

`TwistedWeylMeasureDecompositionStatement` uses the twisted Weyl maps of a
representative set in `WeylTorus F n`, with chosen exact lifts on the regular
norm-image points. Each representative has a measure on the product of its
fixed left quotient and its regular norm-image point set. The local predicate
`WeylTorus.HasTwistedLocalPushforwards` requires an open embedding patch
around each point on which the pushforward of the restricted source measure
is the ambient measure restricted to the patch image.

The local embeddings make the twisted map continuous with open image.
Both the ambient matrix group and the source are second countable. The
countable branch result and the twisted fiber count give the pushforward
on each representative image as the ambient restriction multiplied by the
rational Weyl order.

The disjoint open images cover the σ-regular set by the algebraic
partition. The nonempty images have countably many indices by separability.
Restrict to those indices to apply countable additivity, then restore the
empty images, whose restricted measures vanish. Dividing each pushforward
by its Weyl order gives the sum of measures on the σ-regular set.

This derived step is for the twisted Weyl formula in Henniart–Lemaire
(2011), II.2.10, formula (1). The local pushforward premise will be applied
to the discriminant-weighted product of the quotient measure and the
rational torus measure on its regular norm-image points.
