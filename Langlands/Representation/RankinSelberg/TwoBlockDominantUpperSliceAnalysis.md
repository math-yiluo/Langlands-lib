# Upper slice analysis for the dominant first-block identity

Author: Worker 113.

This internal helper assembles existing analytic results for the upper side of
the strict-dominant first-block identity. Its provenance is JPSS,
*Rankin–Selberg convolutions* (1983), Sections 2.7 and 4.6, together with the
derived determinant-slice formulation used in Section 4.10(2), printed page 419.
The registered original is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The slice packaging and explicit treatment of zero functionals are internal
consequences; they are not claimed to be the source's literal theorem statement.

`exists_uniformOrdinaryJacquetRealization` uses the published factorization
and ordinary convergence proof, whose bound does not require nonzero supplied
functionals. It constructs the ordinary integral at the identity as one linear
functional on all sections. Published equivariance and translation formulas
identify its coefficients with the actual ordinary Jacquet integrals. The
functional is nonzero whenever both supplied block functionals are nonzero.
The same bound and functional precede all quotient measures and test vectors.

`rectangularBorelMeasure` transports the exact supplied finite product measure
along equality of the product and Borel measurable structures, as in the target.
`integrable_rectangularBorelMeasure` transports Schwartz integrability along
the same equality; it introduces no measure map or rescaling.

`continuous_upperAverage` proves continuity for every spectral parameter.
The published finite Schwartz expansion separates the rectangular variable
from finitely many diagonal coefficient integrands. Each diagonal integrand
is continuous by smoothness of both coefficient representations and continuity
of the normalized determinant power. Integrating the finite expansion leaves a
finite sum of these continuous functions times scalar Schwartz integrals.
When the supplied test functional is zero, its entire coefficient model
vanishes and the average is identically zero.

`UpperSliceConverges` means genuine product-space integrability of the actual
unequal-rank integrand at spectral parameter zero, restricted to the indicated
determinant slice and with the supplied additive Haar rectangle measure.
`upperSliceConverges` proves it for full Whittaker-type pairs and every
compatible supplied standard quotient measure. For nonzero functionals, it
restricts published right-half-plane convergence to the product slice and
divides by the nonzero constant spectral weight on that slice. If either
functional is zero, the actual integrand is pointwise zero.

The helper does not assert lower rectangle convergence, the first-block
functional equation, any Laurent cancellation, or factor multiplicativity.
