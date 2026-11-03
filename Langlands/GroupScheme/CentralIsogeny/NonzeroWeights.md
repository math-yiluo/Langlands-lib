# Nonzero adjoint weights through a homomorphism with central kernel

Author: Worker 1283.

This internal supporting unit constructs the linear equivalence
`Lie.nonzeroWeightSpaceEquivRange` from an actual nonzero source adjoint
weight space onto its actual differential image in the target weight
space. The map is induced by `Lie.targetMapLinear` on dual-number identity
kernels. It also proves that every source root remains a root for the
same torus acting on the target through the homomorphism.

The kernel calculation works over every commutative base ring. An actual
Lie vector killed by the differential is a dual-number point in the full
scheme-theoretic kernel. Centrality says that this point commutes with
every point after every test-scheme restriction. In particular it lies in
the whole-torus centralizer. The published
`Lie.mem_weightSpace_zero_of_mem_torusCentralizer` identifies it as a
zero-weight vector.

For injectivity on a nonzero weight space, the base is an arbitrary field,
the source is affine and locally of finite type, the target is affine,
and the acting torus is split. The weight decomposition gives disjoint
spaces for distinct characters. A difference of two vectors with equal
differential image therefore belongs to both the given nonzero weight
space and the zero-weight space, so it vanishes. The equivalence is
`LinearEquiv.ofInjective` for the already published restricted map
`Lie.weightSpaceMap`. Its coercion formula identifies its ambient value
with the actual differential. If the target space of a source root were
zero, the same argument would make the source space zero, proving the
root inclusion.

The proof uses only centrality of the full kernel; it assumes neither
finiteness nor flatness of the homomorphism, and it does not assume that
the homomorphism or its kernel is smooth or separable. The source itself
need not be reductive or connected. All field and scheme types have
arbitrary universe `u`.

This is an internal deduction from the published definitions of central
kernels, actual Lie maps, weight spaces and the split-torus weight
decomposition. It proves one direction of the geometric comparison needed
in the central case of Milne's Proposition 23.5. It does not prove
surjectivity on nonzero target weight spaces, a bijection of root systems,
compatibility of supplied coroots, or
`CentralIsogenyRootDatumHomStatement`.
