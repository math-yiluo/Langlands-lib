# Continuity of the first unfolding averages

This internal helper for the fixed-slice first unfolding of JPSS (1983), Section 4.6,
is derived directly from the published smooth induction and actual integrand data.
It does not claim convergence or integrability.

The open right stabilizer of a section fixes its values at every group element.
Consequently the entire rectangular Jacquet integrand is locally constant in the
group argument, with values in the function space of the rectangle. The definition
`rawIntegrandLocallyConstant` bundles this actual family as a locally constant map.
Postcomposition
by either the signed integral or the integral of the complex-valued norm preserves
local constancy, without requiring continuity of integration on a function space.

For any continuous standard-character function W and row Schwartz–Bruhat function,
the descended integrand is continuous by quotient topology. The representative
formula for the absolute radical average factors it into the norms of W and the
row function and the integral of the norm of the raw Jacquet integrand. This proves
continuity of both radical averages. These are statements about ordinary totalized
Bochner integrals; absolute convergence must still be established separately before
using them in the actual unfolding identity.
