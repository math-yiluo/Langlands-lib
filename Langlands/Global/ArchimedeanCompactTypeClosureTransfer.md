# Closure transfer for actual compact types

Author: Worker 94.

These internal helper theorems implement the topological passage from
an algebraic compact-invariant module to its closure. All spaces,
compact translations and compact-type submodules are the published actual
archimedean objects. The universe, number field and natural rank are
unrestricted.

`compactOrbitClosure_operator_preserves` takes a complex submodule `M`
stable under every actual compact translation. Every vector of `M` is
assumed to have a finite-dimensional compact-orbit span. It also takes a
continuous linear operator `P` whose value on each input lies in the
closure of that input's compact-orbit span. The theorem proves that `P`
preserves `M`. For each input in `M`, its orbit span lies in `M` by
invariance and is closed by finite dimension. The supplied orbit-closure
membership is therefore membership in that span.

`compactType_inf_topologicalClosure_eq` additionally assumes finite dimension of
`M ⊓ compactTypeSubmodule σ` for the selected actual compact type. It proves

`M.topologicalClosure ⊓ compactTypeSubmodule σ =
 M ⊓ compactTypeSubmodule σ`.

The proof obtains one actual continuous operator from the theorem `compactTypeProjection K n`. The first helper proves preservation of
`M`, and `Langlands.Analysis.inf_topologicalClosure_eq_of_projection`
applies the closed inverse-image argument. Compact equivariance of the
chosen projector is available but is not used by this
closure argument.

The projector is constructed in the imported `ArchimedeanCompactTypeProjectionProof`.
Its statement is published; the projector proof and this closure-transfer proof
require independent review and publication. This module does
not assume the projector as an additional mathematical hypothesis. It supplies
no algebraic compact-type dimension bound or orbit-density theorem. Those
inputs must be separately proved before deriving admissibility of a closed
group module, convolution reproduction or automorphic growth.
