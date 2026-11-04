# Pointwise topologies on actual real and complex parameters

This construction supplies the finite-dimensional parameter
topology needed for the topological assertions of Renard 2026 V.3.20,
printed p.116/PDF p.122. It uses the actual valuation image and the
published connected-reductive integer basis. It does not define replacement
groups, character lattices or rational-point topologies.

The registered source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The use of the pointwise topology on the additive dual and the explicit
finite-coordinate comparison is an internal realization of the
finite-dimensional vector-space topology implicit in that passage.

For `Lambda = Additive (rationalDiscreteValuationImage G)`, the named
complex and real parameter topologies are induced by the inclusions
`Hom_Z(Lambda,K) -> (Lambda -> K)`, for `K = C` or `R`, with the product
topology on the function space. These topologies are defined for every
group in the displayed local-field framework, without a basis choice.
They are supplied as named topologies, without globally assigning
topologies to every additive-homomorphism type. The complex topology is used
locally through an explicitly named instance.

For a connected reductive group, evaluation at
`rationalReductiveValuationBasis` identifies the complex and real
parameters linearly with the corresponding finite tuples. The inverse
extends the tuple by integer linearity. The continuous linear
equivalences show that the basis-independent pointwise topology is the
finite-dimensional topology. Forward continuity follows from evaluation;
inverse continuity follows by writing every value as a finite sum of
integer multiples of the coordinates. The basis and its finite rank are
obtained from the existing shared rational-character lattice theorem,
without an additional structural premise.

The complex parameters form a topological additive group, by induction
from the function space. Evaluation is continuous. The existing complex
exponential is continuous into the compact-open character space:
on the discrete image that topology is the pointwise topology, and each
value is the continuous scalar function `exp(-lambda(a) log q)`.

This file does not establish the exact exponential kernel, a quotient
homeomorphism, discreteness or cocompactness of the period subgroup, the
compact imaginary quotient, or the tensor and split-center comparisons.
Those remain separate statement and proof obligations. No claim of full
V.3.20 coverage is made.
