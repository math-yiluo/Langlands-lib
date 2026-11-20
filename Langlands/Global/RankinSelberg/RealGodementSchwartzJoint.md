# Joint convergence of the real Godement integral for Schwartz tests

`RealGodementSchwartzJointStatement` gives joint absolute convergence of the expanded real Godement open-cell integral for an arbitrary rectangular Schwartz test. It assumes the strict chamber and the explicit lower Haar bounds on the real part of the leading exponent. It identifies the original upper Jacquet integral with the first-column value on that region.

The lower-group norm integral, including the absolute determinant weight of the upper argument, is continuous by dominated convergence on compact neighborhoods. The absolute Borel change of variables gives its covariance with the norm of the upper inducing character. The strict-chamber open-cell estimate applies to this continuous function. Its open-cell norm integral is exactly the integral of the norms of the lower slices. Lean combines the integrable slices and the integrable outer norm by the product integrability theorem. The existing change of variables and Fubini identity then identifies the two coefficients.

This implements the joint convergence argument of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2, pp. 47–48, using the explicit right-half-plane estimate for general Schwartz tests and the Library's upper Borel convention.
