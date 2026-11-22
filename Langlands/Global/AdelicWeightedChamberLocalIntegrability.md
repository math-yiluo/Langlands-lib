# Local integrability from a weighted chamber norm

`WeightedChamberLocalIntegrabilityStatement` starts with a measurable function on actual adelic points invariant under left rational translation. Suppose its squared integral with the exponential chamber density is finite on the parabolic fundamental domain. If the open height region meets every rational orbit, the function is locally Haar-integrable on the whole adelic group.

The proof descends the weighted squared integral to the parabolic quotient. At a point in the height region it chooses a compact neighborhood inside the region on which the quotient map is injective. Local integration on a discrete left quotient bounds the ambient weighted squared integral on that neighborhood by the quotient integral. On the compact neighborhood the exponential density has a positive lower bound. This gives an ordinary square-integrable restriction, which is integrable because Haar measure is finite on the compact set. A rational left translate brings an arbitrary point into such a neighborhood and carries the integrability statement back by Haar invariance.

This is derived from the Siegel-domain coverage and weighted norms of Bernstein–Lapid, §7.1, pp. 210–211, and §7.3–7.4, p. 215. The Lean statement takes coverage as a hypothesis and supplies the local integrability used in differentiation of smoothing convolutions.
