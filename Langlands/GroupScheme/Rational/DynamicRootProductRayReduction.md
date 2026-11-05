# Dynamic ordered root products from actual root-ray decomposition

Worker 1315 wrote this internal derived reduction. It proves the full existing
`DynamicRootOrderedProductStatement` with exactly one structural proposition
remaining as a premise: `RelativeRootRayDecompositionStatement`. It does not
prove that premise or the unconditional host target.

`hasOrderedSemigroupProducts_of_unipotent` applies over any field in arbitrary
universe `u`. The original group is smooth, connected, affine and unipotent,
and the acting torus is split. For its actual automorphic action, the conclusion
is `HasOrderedSemigroupProducts`: every finite ordered partition of the complete
occurring Lie-weight support, with disjoint original blocks and the original
block-versus-positive-closure exclusion, has smooth connected closed
representatives of its actual semigroup subgroups, and their original ordered
multiplication is an isomorphism of schemes over the original field.

The proof applies
[`HasOrderedSemigroupProducts.of_fieldExtension`](SemigroupFieldReduction.md)
to the algebraic closure in the same universe. Affineness and smoothness persist
by pullback. The published geometric-connectedness theorem gives connectedness
of the base change, and
[`IsUnipotent.baseChange`](../Unipotent/BaseChange.md) gives its unipotence.
The split torus and the actual action also pull back. The unconditional
[`unipotentSemigroupOrderedProduct`](UnipotentSemigroupProductProof.md)
then supplies the exact algebraically closed unipotent property. Field-extension
detection descends it to the original action. That imported detection theorem
constructs original-field representatives by geometric realization and compares
their actual base changes and ordered multiplication. No descent datum or
original-field product conclusion is assumed here. No solvability or splitness
premise is added to the original unipotent group.

`DynamicRootOrderedProductFromRays` is the proposition
`RelativeRootRayDecompositionStatement → DynamicRootOrderedProductStatement`
at the same arbitrary universe. The theorem
`dynamicRootOrderedProduct_of_rayDecomposition` proves it using the restricted
source assembly in
[`DynamicRootProductAssembly`](DynamicRootProductAssembly.md). The positive
semigroup realization there is smooth, connected, closed, unipotent and split
unipotent, so the preceding arbitrary-field theorem supplies all needed source
products directly. The published `semigroupRealization`,
`dynamicSemigroupComparison` and `cyclicRootFunctorComparison` supply the other
premises. Actual relative roots are nonzero by their definition, so the last
comparison applies to every required factor without a root-uniqueness premise.

The unchanged construction identifies the positive source's actual Lie support
with the positive relative roots, uses the supplied disjoint rays to partition
that support, and maps its semigroup factors back into the ambient group.
Their full cyclic-tail comparison gives exactly the actual relative-root
subgroups. The isomorphism is the source ordered multiplication; postcomposition
with the radical inclusion is exactly the ambient ordered multiplication.
The conclusion retains arbitrary fields and cocharacters, every injective
ordering, zero and nongeneric cocharacters, the empty product, and the complete
indivisible-root factors including doubled-root subgroups. It gives smooth
connected closed split-unipotent representatives for the radical and every
factor, as required by the unchanged target.

This is a substantive specialization to the positive unipotent source. It
removes the general solvable ordered-product theorem from the required inputs;
it does not prove that separate theorem, choose a maximal-torus decomposition,
or replace ray separation with a hypothesis on the field. The remaining
ray-decomposition proposition is explicit. In particular, acceptance of this
supporting implication is not completion of the unconditional product task.
The provenance is internal composition of the published realization,
unipotent product, field-extension detection and comparison proofs. It adds
no new external structural assertion or axiom.
