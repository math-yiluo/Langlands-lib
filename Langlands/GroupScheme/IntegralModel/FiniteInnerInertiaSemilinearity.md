# All-automorphism compatibility of the recovered inertia comparison

This internal unit derives compatibility from actual coefficient tower
comparisons. No original-literature theorem is claimed.

`pullbackComparison_transport_semilinear` assumes a finite comparison f
between base changes of two groups, the canonical semilinear action on
its source, an arbitrary specified action on its target, and the
compatibility of the target tower map with an upstairs action.
It proves that conjugating f through the two actual tower comparisons
is compatible with the upstairs actions. The implemented proof uses
`pullbackComparison_semilinear`, naturality of `squareComparison`, the
finite compatibility identity, and cancellation of the source tower
comparison with its inverse.

`galoisBaseMap_restrictNormal_commutes` identifies the actual commuting
square for every automorphism of the inertia fixed field and its
restriction to E. The proof is the contravariant spectrum form of
`AlgEquiv.restrictNormal_commutes`.

`finiteInnerInertiaGenericComparison_semilinear` retains all inputs of
the finite inner solution and additionally assumes exact cocycle
recovery for every inertia-field automorphism, as supplied by common
finite recovery. It extends the finite semilinearity theorem using the
general tower-transport lemma. The target compatibility is precisely
`pullbackComparison_innerGaloisDescentIso`, with the extended finite
conjugator replaced by the prescribed upstairs value using that exact
recovery. Thus the entire recovered generic comparison intertwines the
canonical action on the descended group with the prescribed inner
Galois action for every upstairs automorphism. It neither identifies
the descended F-group with G nor asserts a residue or chamber result.

`InnerGaloisCompatible` is the Prop-valued predicate that a specified
comparison between two actual field extensions intertwines canonical
Galois transport on its source with the inner twist by the prescribed
cocycle values on its target, for every field automorphism. It imposes
no cocycle law by itself. The final theorem packages the proved
all-automorphism identity for the recovered comparison in this predicate.
