# Compact finiteness of the actual lower mixed fiber kernels

Module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper`.
Author: Worker 1196.

This is derived topological and measure-theoretic support for the actual kernels
motivated by JPSS (1983), Section 4.9, equations (2) and (8), printed pages 416
and 418, source `jpss-1983-rankin-selberg`. The properness and common-cover
arguments are internal proofs, not assertions quoted from the source. The
module imports the published actual lower mixed subgroup/fiber definitions and
the companion measurable kernel constructions. It preserves the canonical
p-adic topology and Borel structures, all positive block sizes, the field
universe and all integer small determinant slices.

For a lower mixed matrix `l = [[a0,0],[X,n]]`, `rightRadicalCoord` is `n⁻¹ X`.
It is continuous by continuity of the diagonal coordinates, inversion, entries
and matrix multiplication. `rightRadicalCoord_mixed_mul_radical` proves that
this coordinate recovers `Z` from `diag(a0,n) R(Z)`. The proof uses the published
commutation law to write that matrix in the lower product coordinates, and
then cancels the two invertible diagonal factors.

`quotientFiber_isCompact_preimage_of_coordinate` proves a general lifting
lemma. In a locally compact Hausdorff topological group, let `H ≤ L` be closed
subgroups, let `f : X → G` be continuous with image in `L`, and suppose a
continuous `r : L → X` satisfies `r(b f(x)) = x` for every `b ∈ H`. Then every
map `x ↦ [f(x) g]` has compact preimages of compact subsets of `H \ G`.
The proof lifts the compact quotient set to a compact set `C` in `G`, intersects
`C g⁻¹` with the closed subgroup `L`, and applies `r`. Equality of quotient
classes puts each required point in this compact coordinate image. The
preimage is closed because the quotient by `H` is Hausdorff, so it is compact.
Applying this lemma with `H = M`, `L = Lminus` and `f = R` gives
`radicalFiberPoint_isCompact_preimage` for the actual mixed quotient.

`lowerMixedFirstQuotient` takes the small unipotent quotient of the first
diagonal block of an element of `Lminus`. It is continuous.
`lowerMixedFirstQuotient_lower_mul` shows that its value on `b I(u)`, for
`b ∈ Hminus` and norm-one `u`, is `[u]`. The implementation computes the first
diagonal block of the product as `n_a u`; the upper-unipotent factor disappears
in the small quotient.

`firstBlockFiberPoint_slice_isCompact_preimage` proves compactness after
restriction to any small determinant slice `k`. For a nonempty preimage,
choose a representative `u0` in that slice. Lift the compact target set to
`C` in the ambient group and intersect `C g⁻¹ I(u0)⁻¹` with `Lminus`.
The continuous map `l ↦ lowerMixedFirstQuotient(l) u0` has compact image.
For every other representative `u` in the slice, `u u0⁻¹` is norm-one, and
quotient equality supplies the lower unipotent factor needed for the
coordinate formula. Thus the slice preimage is a closed subset of this compact
image. The empty case is immediate. The closedness of the slice is essential
in this argument.

For every supplied rectangular additive Haar measure, `radicalKernel_compact_ne_top`
proves that each radical kernel measure is finite on compact sets by its exact
pushforward formula and the radical properness result. For every s-finite
small quotient measure that is finite on compact sets and satisfies
`NormOneRightInvariant`, `firstBlockKernel_compact_ne_top` proves the analogous
fact for every slice kernel, using restriction and slice properness.

Finally `radicalKernel_isSFinite` and `firstBlockKernel_isSFinite` apply the
existing `kernel_isSFinite_of_compact_finite` theorem. Each actual target
quotient is Hausdorff, locally compact and second countable, hence admits one
countable compact cover shared by all fibers. This establishes s-finiteness
of the kernels themselves, in addition to finiteness of individual fibers on
compact sets.

The module does not assert existence or normalization of the lower mixed Haar
measure, compatibility of quotient measures, either normalized tower identity,
or any representation-specific convergence theorem. Those remain separate
obligations of the linked integration proof.
