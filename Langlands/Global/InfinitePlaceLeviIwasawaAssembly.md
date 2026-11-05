# Archimedean Levi-compatible Iwasawa from the remaining structural inputs

Author: Worker 1655.

This internal conditional assembly constructs a compatible compact subgroup
of the original completion-point group from three explicit universal
structural premises: adjoint-stable closed realization of connected
reductive groups, rational parabolic classification by dynamic
cocharacters, and the geometric radical theorem for dynamic identity-limit
subgroups. None of those premises is proved here. The exact unconditional
host proposition remains open.

The three premise declarations are respectively
`ConnectedReductiveSelfAdjointRealizationStatement`,
`ParabolicDynamicStatement`, and
`DynamicGeometricUnipotentRadicalStatement`, each at the same arbitrary
universe `u` as the number field. The first supplies an actual closed
matrix representation of each connected reductive group over every
`RCLike` coefficient field with adjoint-stable rational-point image.
The latter two supply the hypotheses of the published
`DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` theorem. They
are universal structural premises, rather than an assumed compact,
decomposition, or point-topology identification.

`completion_realization_of_selfAdjoint_of_dynamic` first applies that
common-cocharacter theorem over the original number field `F`. It obtains
one actual `χ : 𝔾_m → G` whose dynamic parabolic is the range of the
original inclusion `p` and whose dynamic centralizer is the range of the
original composite `l ≫ p`, on all test schemes. Closedness of `p` and
`l ≫ p` makes these actual representatives. Base change of the cocharacter
and the two representation certificates gives the same two represented
dynamic subgroups over `v.Completion`: the proof uses
`parabolic_baseChange`, `centralizer_baseChange`, and preservation of
composition by the base-change functor. It does not choose a minimal
parabolic, so no minimality-preservation assertion is needed.

The previously proved completion theorem supplies an `RCLike` structure
compatible with the completion's original normed field structure. The
published connected-reductive field-extension theorem applies to the
actual pullback of `G`. The adjoint-realization premise then gives its
ambient closed star realization. The arbitrary-`RCLike` internal
conjugation construction supplies compatible diagonal realization of the
same base-changed `p` and `l ≫ p`. This discharges the exact
`HasCompletionDiagonalStarLeviRealization` predicate, with all extension
and real/complex comparisons internal to the construction.

`exists_leviCompatibleIwasawaCompact_of_selfAdjoint_of_dynamic` passes
this realization to the published actual-completion transport theorem.
That theorem uses multiplicative homeomorphisms on the actual point
groups with their regular-function evaluation topologies. It preserves
maximal compactness in the ambient group, the product with parabolic
image on the left, equality of the parabolic and specified Levi
intersections with the compact, and maximal compactness of the inverse
image on the original Levi carrier. The rational Levi hypothesis supplies
its affineness for the topology transport. Thus the result is exactly
`IsLeviCompatibleIwasawaCompact` on `InfinitePlaceGroupPoints F G v`,
including the existing `K.comap` formulation for the last clause.

`leviCompatibleIwasawaCompact` chooses this actual subgroup, and
`leviCompatibleIwasawaCompact_spec` establishes all four properties for
the same choice. The final conditional wrapper returns the unchanged
`LeviCompatibleIwasawaStatement` after taking the three structural
premises. It is not the unconditional closing theorem: none of those
premises is a proof available from its statement definition. Non-split
and anisotropic groups, improper parabolics, and arbitrary universe are
retained without added rank or splitness assumptions.

The provenance is internal composition of the published
common-cocharacter construction, all-test base-change identities,
connected-reductive field extension, the real/complex internal conjugation
construction, and the already proved actual-completion topology
transport. No new external structural assertion is attributed to an
original source by this module.
