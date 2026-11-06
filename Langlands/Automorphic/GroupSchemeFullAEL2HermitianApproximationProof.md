# One Hermitian approximation on the original quotient and full cusp L2 spaces: proof

`groupSchemeFullAEL2HermitianApproximation` proves the exact proposition
`GroupSchemeFullAEL2HermitianApproximationStatement`.

The proof takes the real sequence and its integrability, weight,
support, ambient symmetric contraction and strong-convergence properties
from `groupSchemeQuotientL2HermitianApproximation`. It defines the full
cusp operators using precisely those same weights and inverse canonical
group Haar measure.

The already constructed `fullAEL2CuspidalIntegratedAction_val` identifies
each included cusp operator with the ambient operator on the included
vector. The inherited submodule inner product therefore transfers
ambient symmetry. The same exact inclusion and inherited norm transfer
the ambient operator norm bound to the cusp operator by
`ContinuousLinearMap.opNorm_le_bound`. Strong convergence in the full
cusp carrier follows from ambient convergence and the criterion
`tendsto_subtype_rng` for its original induced topology. No separate
approximation sequence or approximation theorem for the cusp
representation is used.

Finally the original integrated-action laws give the subtype-valued and
ambient orthogonal projection identities for every chosen weight and
index. These use the actual projection from the whole original quotient
L2 space onto its full all-parabolic AE cusp subspace. Absolute Bochner
integrability and projection equivariance are supplied by the imported
integration construction.

This internal proof retains the hypotheses and the qualified continuous
full-group scope of its target. The exact target, the ambient quotient
approximation proof and the full cusp integration construction it uses
are all in the published Library; this proof is submitted on its own
against that exact target. It claims no smoothness, smooth-vector
density, compactness, trace or spectral result.
