# Actual-root detection of parabolic inclusion through Lie algebras

This internal derived module proves a weight-span order criterion and the
parabolic half of the actual-root sign inclusion target. Its only unproved
structural premise is the published proposition `DynamicConnectedStatement`.
It makes no claim to prove the full `RelativeRootSignInclusionsStatement`.

For any split-torus action on an affine group locally of finite type over an
arbitrary field, `semigroupWeightSpan_le_iff_on_weightSupport` identifies
inclusion between semigroup weight spans with containment of the semigroups
after restriction to nonzero ambient weight spaces. For the forward direction,
a nonzero vector in an excluded weight space contradicts the disjointness of
that space from the target span. For the reverse direction, each source
weight space either vanishes or has an index in the target semigroup.
These are consequences of the intrinsic split-torus weight decomposition
implemented in `SemigroupWeightSupport`; no realization of semigroups by
subgroup schemes is used.

The published theorem `dynamicLie` and the cocharacter weight-sum comparison
identify the tangent submodule of each dynamic parabolic with its nonnegative
torus weight span. Parabolic containment therefore implies the actual-root sign
condition without smoothness or connectedness. The conversion between ambient
weight support and actual roots uses `RelativeRootSignSupport`, whose zero
character case is automatic.

Conversely, for a smooth connected affine ambient group, the sign condition
gives inclusion of the nonnegative weight sums. The published theorem
`parabolic_le_parabolic_of_lieKernel` upgrades this to containment on every test
scheme. Its smoothness and full-Lie subgroup-equality premises are discharged
by the published proofs `dynamicSmooth` and `lieSubgroupEquality`. Its dynamic
connectedness premise remains explicit. The second cocharacter lies in the first
parabolic because both factor through the same commutative group scheme.

`RootSignParabolicInclusionsFromConnectedness` packages precisely this
conditional result. It allows any split torus acting through any homomorphism
into a smooth connected affine group, so neither reductivity nor maximality
is required for this parabolic result. The construction is internal and derived
from the cited Library modules; the structural dynamic Lie and smoothness inputs
implement Conrad–Gabber–Prasad, Proposition 2.1.8, and subgroup equality implements
Milne, *Algebraic Groups*, Proposition 10.15 with Proposition 1.37.
