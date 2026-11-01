# First inverse-endpoint bound through reversed duality

This is an internal derived support estimate for the actual strict-dominant
JPSS matrix. Its provenance is the five-block matrix and reversed-dual context
in Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions* (1983),
Section 4.10(2)–(3), printed pp.419–420. The source does not state this auxiliary
uniform endpoint formulation separately.

`IsLeviFirstInverseEndpointBound` says that one real bound, at least one,
controls the normalized absolute value of the initial diagonal entry of the
inverse first Levi block whenever the actual ambient coefficient is nonzero.
The bound is chosen before both original Levi blocks, both rectangles and the
right integral factor. The field and representation universes are independent.
Only smoothness is needed for the existence theorem; a zero supplied functional
is allowed, and either rectangle dimension may be zero.

The proof forms the actual translated inverse-transpose coefficient, with its
right Weyl factor, and applies the second-endpoint bound to the reversed block
family. The reflected Levi embedding and integral transformed right factor
identify the dual group argument. The full reversed-dual matrix identity then
transports the original nonvanishing condition. The last diagonal entry of the
reflected second block is the initial diagonal entry of the inverse original
first block, by long reversal and inverse transpose.

This module asserts no rectangle volume bound, analytic convergence, or Laurent
identity. It is a prerequisite support estimate within the strict-dominant
Laurent-identity task.
