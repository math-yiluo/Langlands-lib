# Compact finiteness and s-finiteness of the radical fiber kernel

Authors: Worker 113 and Worker 235. Internal derived support for the unchanged
two-block unipotent quotient integration statement. Worker 235 supplied the
coordinate homeomorphism and radical-coordinate API used in the compactness
proof; Worker 113 supplied the compactness proof and the kernel consequences.

`fiberPoint_isCompact_preimage` proves that the radical fiber map
`x ↦ [u(x) g]_H` has compact preimages of compact sets. Here the two positive
block ranks sum to the ambient rank, the field is a Hausdorff topological ring,
and its general linear group is a locally compact topological group. The
quotient is the published actual left-coset space by the block-diagonal
unipotent subgroup `H`, with its existing quotient topology.

Lift a compact set of left block cosets to a compact set C in the ambient group
using `leftQuotient_exists_isCompact_image`. If [u(x) g] lies in that set, there
is c in C and b in the block subgroup with c g⁻¹ = b u(x).
This matrix lies in the full unipotent subgroup and has radical coordinate x.
The full unipotent subgroup is closed, so its intersection with C g⁻¹ is compact.
The continuous radical coordinate sends this intersection to a compact set
containing the fiber preimage. The preimage is closed, because the block quotient
is Hausdorff, and is therefore compact.

For the canonical topology on a `PadicField`, `fiberKernel_compact_ne_top` proves
that every fiber of the actual `fiberKernel F h μ` is finite on compact sets.
Quotient induction and `fiberKernel_mk` identify its value with the pushforward
of the supplied rectangular additive Haar measure μ. The pushforward mass of a
compact set is μ of its compact preimage by the preceding theorem. Additive Haar
measures are finite on compact sets. The arbitrary supplied Haar measure is
retained unchanged, and the theorem permits arbitrary Borel measurable structures
compatible with the fixed topologies.

`FiberKernelSFiniteStatement F h` is the proposition that every supplied
rectangular additive Haar yields an s-finite actual kernel. Its proof,
`fiberKernel_isSFinite`, installs local compactness, second countability and
Hausdorffness of the actual block quotient. Local compactness and second
countability give a countable compact cover. Applying
`kernel_isSFinite_of_compact_finite` to the preceding compact mass bound proves
`IsSFiniteKernel (fiberKernel F h μ)`. The argument needs no measurable choice of
coset representatives and no uniform bound on the total masses of the fibers.

These results are internal consequences of the published quotient topology and
block/radical definitions, Worker 235's coordinate homeomorphism, and the
measurable-kernel support lemmas. No separate literature theorem is claimed.
The module establishes neither the normalized quotient-measure tower nor the
final integration statement.
