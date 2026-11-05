# Extending a Tits system by a supplement

This internal algebraic transport is a representative-projection form of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 1.4.12(2), printed
pages 51–52 (PDF pages 82–83). A normal subgroup `H` carries the restricted Tits
system. Every ambient element is a product of an element of `H` and a supplement
`T`. The supplement lies in both target distinguished subgroups; the normalizer
normalizes it. The target Weyl projection agrees with the source projection on
restricted representatives and kills the supplement.

`TitsSystem.restrictedInclusion H N` is the actual inclusion homomorphism
from `N.subgroupOf H` to `N`, obtained by forgetting membership in `H`.
`exists_restricted_factor` factors an element of any subgroup containing the
supplement into a restricted element and a supplement element.

`TitsSystem.extension` transports the Tits axioms to the ambient group with the
same Weyl group and simple reflections. Its hypotheses expose factorization and
projection compatibility rather than constructing a Weyl-group quotient. The proof
factors the target Borel and normalizer elements into restricted elements and
supplement elements, and moves supplement factors to the right. The restricted
multiplication axiom then gives the target multiplication axiom. A conjugated
source witness gives the target nondegeneracy witness. Generation and the kernel
identity follow from the same factorizations.

This helper does not supply the actual group-theoretic or geometric inputs for
an affine Iwahori–Tits system.

`TitsSystem.IsSaturated.extension` proves the saturation equality from saturation
of the restricted pair and the target Tits axioms, using the same supplement
factorization, containments and normalizer condition. It does not require
normality of `H`. An element in every target conjugate is in `B`, so it factors
as `b t` with `b` restricted. Removing the conjugated supplement proves that `b`
lies in every restricted conjugate; source saturation then puts `b` in `N`.
The reverse containment follows from the target projection's kernel identity.
