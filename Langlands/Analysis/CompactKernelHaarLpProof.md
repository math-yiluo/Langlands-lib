# Properness and Haar/Lp transport for compact-kernel homomorphisms

Author: Worker 117.

This is an internal derived proof of
`Langlands.CompactKernelHaarLpComparisonStatement`, using the pinned Mathlib
topology, Haar uniqueness and Lp results. It is not attributed to a separate
assertion in the literature. The group, quotient and function-value universes
are independent.

`Langlands.compactKernelProperMap` first identifies the saturation of a set
`S` under the actual homomorphism `q` with the product `S * q.ker`. A product of
a closed set with a compact set is closed in a topological group. Since the
continuous open surjection `q` is a quotient map, this proves that `q` is
closed. For each `y`, surjectivity supplies `x` with `q x = y`; the fiber over
`y` is the image of the compact kernel under left translation by `x`. Thus
all fibers are compact. Mathlib's closed-map and compact-fiber criterion
proves `IsProperMap q`. This step uses no measures or second countability.

`Langlands.compactKernelHaarLpMeasure` extracts the cocompact-filter condition
from properness and applies `MeasureTheory.Measure.isHaarMeasure_map` to
the actual pushforward `Measure.map q μ`. On the second-countable target,
Haar uniqueness expresses this pushforward as `haarScalarFactor` times `ν`.
The factor is a nonnegative real, hence finite; positivity for two Haar
measures makes its real coercion strictly positive. The proof converts its
extended nonnegative coercion to the required `ENNReal.ofReal` expression.

For a continuous `f : H → E`, second countability of the source `H` supplies
strong measurability of `f`, without separability or completeness of `E`.
The map-measure Lp equivalence identifies membership of `f ∘ q` with
membership of `f` for the pushforward. Haar uniqueness and finite measure
scaling transfer membership between the pushforward and `ν` in both
directions, using the two scalar factors with the measures exchanged.
The Mathlib lemmas apply to every extended nonnegative exponent, including
zero and infinity.

`Langlands.compactKernelHaarLpComparison` assembles these two proofs into
the exact published conjunction. No properness premise, second countability
of `G`, normalization of Haar measures, or additional condition on `E` is
introduced. The statement and its imported definitions are unchanged.
This generic result does not construct reductive rational-point topologies
or prove compactness of a representation-theoretic central quotient.
