# Gluing affine normal quotients over an open base cover

This auxiliary module constructs a global affine group quotient from supplied local
affine fppf quotients. The base scheme and universe are unrestricted. The ambient
group is affine and locally of finite type over the base, the represented subgroup
is monomorphic and smooth, and its all-test range is normal.

`AffineNormalQuotientOpenGluingStatement` assumes an open cover of the base and,
over each cover member, an affine group scheme with an fppf quotient map from the
base-changed ambient group. The kernel range must equal the range of the
base-changed subgroup inclusion on every test scheme. Its conclusion is an
actual affine group scheme over the original base and an fppf quotient map with
the original subgroup as its full kernel.

The implemented proof first constructs the canonical étale sheafification of
right cosets by the smooth subgroup. Published smooth-relation quotient results
make this an fppf sheaf whose canonical projection is smooth and surjective.
The published exact-relation comparison identifies equality of canonical
quotient sections with membership of the difference in the subgroup range.

Restriction of a presentation to any base scheme uses the actual pullback of
its source. Continuity of the functor between slice sites preserves the sheaf
condition, and cocontinuity preserves local surjectivity. Each supplied local
fppf quotient has exactly the same sectionwise fibers as this restricted
presentation. The published common-kernel comparison therefore gives a
representation of the restricted sheaf by the prescribed local quotient.

The published open-cover representation gluing theorem gives a global
representative; affineness descends by its local-representation property
criterion. Full faithfulness of lifted Yoneda gives a global projection. It is
smooth and surjective by the original canonical projection's represented
base-change properties. It is quasi-compact because the source is affine over
the base and the target is affine, hence quasi-separated, over the base.
The exact coset fibers pass through the representing isomorphism. Finally the
published normal quotient construction descends the group operations, and its
kernel theorem yields the required fppf quotient.

The auxiliary `RelativeRoot.IsFppfQuotient.fibers` rewrites equality of quotient
images as membership of the difference in its full kernel. This concerns all
test schemes, not merely field-valued points.

This module is derived solely from existing Library results and introduces no
external-source assertion. It is part of the quotient existence proof for
relative parabolics. Supplying the local quotients, descending them from étale
neighborhoods, proving reductivity of the glued target, and the universal
factorization property are not part of this module: étale descent is in
`NormalQuotientEtaleGluing`, reductivity of the glued target in
`NormalQuotientReductiveGluing`, and the complete quotient theorem is
`relativeParabolicReductiveQuotient` in `RelativeLevi.ReductiveQuotientProof`.
