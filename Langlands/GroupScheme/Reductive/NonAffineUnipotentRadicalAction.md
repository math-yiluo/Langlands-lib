# Smooth automorphic actions on radicals without affine hypotheses

This internal derived module proves that a smooth group acting by
automorphisms preserves any supplied represented unipotent radical over an
algebraically closed field in arbitrary universe `u`. Neither the target group
nor its radical is assumed affine, and the target need not be connected or
smooth. The existing full radical predicate is used throughout.

`IsClosedSubgroup.exists_overFactor_of_algClosed_points` first gives a
factorization criterion for an arbitrary morphism from a reduced scheme locally
of finite type over the field into the ambient group. If every rational point
factors through the supplied closed subgroup, the whole morphism does. The
proof pulls back the closed immersion. Its range is closed and contains all
closed points, since over an algebraically closed field those points have
rational sections. Closed points are dense by the Jacobson property. The
pullback is therefore a surjective closed immersion into a reduced scheme and
is an isomorphism. Its inverse gives the actual factorization.

For an automorphic action of a smooth `H` on `G` and a supplied radical
`i : U → G`, the action restricted to `H × U` has a smooth, hence reduced,
source locally of finite type. At each rational point `(h,u)`, the section `h`
induces an actual automorphism of `G`. Ambient isomorphism transport and
uniqueness of represented radicals show that it preserves the all-test image
of `i`. The factorization criterion therefore factors the restricted action
morphism through `U`. Evaluating that factorization on every relative scheme
test proves `IsUnipotentRadical.isStable_of_smooth`, including tests that are
nonreduced.

`IsUnipotentRadical.actionOfSmooth` then uses the existing action construction
on a represented stable subgroup. Its action laws follow from the representing
monomorphism. `actionOfSmooth_isEquivariant` states that the actual inclusion
intertwines the induced and original actions.

The argument extends the published affine action result by replacing its
quotient-kernel argument with direct factorization through the closed radical.
It uses only internal subgroup comparison, ambient isomorphism transport,
smooth reducedness, and closed-point geometry. It does not assert existence
of a radical or preservation under field extension.
