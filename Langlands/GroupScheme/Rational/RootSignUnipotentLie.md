# Actual-root detection of unipotent inclusion through Lie algebras

For every smooth affine group over an arbitrary field and every homomorphism
from a split torus into that group, this internal derived module proves that
dynamic identity-limit subgroup inclusion is equivalent to containment of the
strictly positive regions on actual relative roots. The proposition
`RootSignUnipotentInclusionsStatement` packages this equivalence at the original
universe `u`; `rootSignUnipotentInclusions` proves it. Neither connectedness of
the ambient group, reductivity nor maximality of the split torus is required.
There is no dynamic connectedness premise in this radical result.

For any multiplicative-group action on a smooth connected affine group,
`AutomorphicAction.unipotent_eq_top_of_lieKernel` proves that the identity-limit
subgroup is the whole group if every Lie vector lies in that subgroup. The
proof uses the closed representative and its smoothness from
`Dynamic.ActionAffineRepresentability`. That module constructs the representative
in the semidirect product by the multiplicative group and factors it through the
normal factor using `semidirectUnipotentLift`; its smoothness follows from
`dynamicSmooth`. The full Lie algebra of the factored closed inclusion then gives
equality on every test scheme by `lieSubgroupEquality`.

`Dynamic.unipotent_le_of_lieKernel_of_smooth` compares two identity-limit
subgroups associated with cocharacters in a common commutative group. Represent
the first by a smooth affine group `H`. The published theorem
`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent` from
`Dynamic.UnipotentConnected` proves that `H` is connected, using the polynomial
contraction of the actual dynamic unipotent representative. Commutativity
preserves the first subgroup under the second action, so the second action
induces an actual action on `H`. Its identity-limit subgroup is the inverse
image of the second ambient unipotent subgroup along the closed inclusion.
Inclusion of the ambient Lie kernels therefore implies that all Lie vectors
of `H` lie in this induced identity-limit subgroup. The preceding lemma makes
that subgroup all of `H`, proving inclusion on every original test scheme.
The common commutative group need not be a torus for this Lie-kernel lemma.

The exact Lie criterion `dynamicLie` and the cocharacter weight-sum comparison
identify the tangent submodule of each dynamic unipotent subgroup with the
positive torus weight span. The generic weight-span order criterion from
`RootSignParabolicLie` converts positive actual-root sign containment to Lie
kernel containment, and hence to unipotent inclusion. This proves
`RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth`. The reverse
implication also follows from the tangent submodule comparison and requires
only affineness and local finite type, without smoothness or connectedness.
The equivalence is stronger in conclusion than the sufficient direction asked
for by the original full target.

The earlier conditional interfaces `Dynamic.unipotent_le_of_lieKernel` and
`RelativeRoot.unipotent_le_iff_positive_rootSupport` retain their types and are
wrappers around these unconditional results. The existing proposition
`RelativeRootSignInclusionsFromConnectedness` retains its type and its proof
combines the parabolic criterion from `RootSignParabolicLie` with the radical
criterion here in the original arbitrary-field connected-reductive
maximal-split-torus setting. Dynamic connectedness is still used for its
parabolic half, so this module does not prove the unconditional full
`RelativeRootSignInclusionsStatement`.

This construction is derived internally from the named Library modules; no
semigroup realization or dynamic-semigroup comparison premise is used. The
structural dynamic Lie, smoothness and unipotent contraction inputs implement
Conrad–Gabber–Prasad, Proposition 2.1.8, and subgroup equality implements Milne,
*Algebraic Groups*, Proposition 10.15 with Proposition 1.37.
