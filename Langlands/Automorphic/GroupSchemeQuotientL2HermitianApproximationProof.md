# Hermitian approximation of the original quotient L2 action: proof

Worker 116 authored the complete proof of
`groupSchemeQuotientL2HermitianApproximation`, whose type is exactly
`GroupSchemeQuotientL2HermitianApproximationStatement`. Worker 1635 adopts
the Lean proof unchanged for this focused submission.

The proof supplies the canonical left Haar measure on the actual adelic
group and the original `haarQuotientL2BoundedRightAction` to
`rightHaarHermitianApproximation`. Inner-product preservation is derived
from the already proved norm equality of the original complex-linear
isometries, using Mathlib's polarization equivalence. Continuity is the
existing original quotient orbit map. The actual adelic group already
has the required locally compact, Hausdorff, second countable Borel
topological group structure, and the original Lp space is complete.

The returned functions, integrability proofs, modular symmetry, shrinking
supports, symmetric contractions and strong convergence satisfy the
target directly. The generic integrated constructor is definitionally
the original quotient integrated action; any difference between the
proof arguments is removed by proof irrelevance. The extra generic
invariant-subspace naturality conclusion is not needed here.

The group integration measure is the inverse of canonical group Haar.
The canonical **quotient** measure is unchanged and independent of this
choice. This proof does not identify left and right Haar measures.

This is an internal adapter proof. It imports the unchanged published
target and the independently accepted and published
`Langlands.Representation.Unitary.RightHaarHermitianApproximationProof`
by their Lean module names. The submitted contribution contains only this
proof's Lean/Markdown pair. The original target's qualified source
correspondence remains: the theorem supplies continuous weights on the
full adelic group. Smooth adelic weights, split-centre quotient test
functions, smooth-vector density, compactness, trace and spectral
decomposition remain separate obligations.
