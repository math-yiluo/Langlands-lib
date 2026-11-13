# Reduction of local quaternionic spin groups to two geometric statements

Author: Worker 97.

This derived module proves a conditional assembly result for Task 5397. At any
universe `u`, `LocalSpinRankOneReductionStatement` is the implication from the
published `OrdinaryOrthogonalGeometryStatement` and
`QuaternionicMoritaIsometryStatement` to the exact, unchanged
`LocalSpinRankOneStatement`. The theorem `localSpinRankOneReduction` proves this
implication. Neither geometric proposition is proved here, and the implication
does not constitute an unconditional proof of the local spin statement.

The helper
`FirstKindInvolution.smooth_and_isAbsolutelyAlmostSimple_of_geometry` works over
every field, with no local-field, Witt-index or characteristic assumption. Its
algebra is a central quaternion division algebra `D` over `K`; the involution
has a symmetric subspace of dimension three; the rank `m` is at least three;
and the quadratic form is nondegenerate in the published polar sense. It
asserts smoothness of the actual isometry group and absolute almost simplicity
of its actual identity component, with the smoothness witness preceding that
component.

The implemented proof first applies the Morita proposition. This gives a
nondegenerate scalar quadratic form `Q` of rank `2 * m` over `AlgebraicClosure K`
and an actual group-scheme isomorphism from the base change of the quaternionic
isometry group to the scalar isometry group of `Q`. Applying the ordinary
orthogonal proposition to `Q` gives smoothness and absolute almost simplicity
of the scalar identity component. The published
`IdentityComponent.smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso`
then descends both conclusions to `K`. The maps `toAlgebraicClosure K` and
`algebraBaseMap K (AlgebraicClosure K)` are the same canonical scalar-extension
map in the imported definitions. This step uses a group-scheme isomorphism,
not just a correspondence of rational points.

For the local spin conclusion, the allowed ranks four and five are each at
least three. The helper therefore gives a smooth isometry group and an
absolutely almost-simple identity component. Its almost simplicity implies
semisimplicity, so
`FirstKindInvolution.exists_isSpinCover_of_isSemisimple` supplies a spin cover.
The published local-field infinitude theorem supplies `Infinite K`, and
`FirstKindInvolution.splitRank_connectedIsometryGroup_eq_one` computes the
identity component's split rank from nondegeneracy and quadratic Witt index
one. Finally,
`IsSpinCover.properties_of_connectedIsometryGroup` gives simple connectedness,
almost simplicity and split rank one for every supplied spin cover.

All objects and predicates are imported unchanged. Both geometric assumptions
range over arbitrary characteristic, including two, and the proof introduces
no characteristic restriction. Provenance is entirely derived: this module
composes the named published statements and theorems and makes no additional
claim about the original literature. Actual proofs of the two geometric
propositions remain separate prerequisites for the unconditional host theorem.
