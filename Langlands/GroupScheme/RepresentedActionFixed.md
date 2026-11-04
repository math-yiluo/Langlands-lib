# Fixed subgroups of represented invariant subgroups

This module gives internal comparisons for the published actual-action and
represented-subgroup constructions. Its base is an arbitrary scheme, and its
universe is arbitrary. Every fixed-point assertion includes every refinement of
every test scheme. No field, affineness, smoothness or finiteness hypothesis is
used.

Let `a` act on `G`, let `b` act on `C`, and let `i : C ⟶ G` be a
monomorphism intertwining the two actions on all tests.
`isFixed_iff_of_equivariant_mono` proves that a `C`-point is fixed for `b`
exactly when its image is fixed for `a`. The forward direction composes each
refined fixed-point equation with `i`; the reverse direction cancels `i` in
each equation. `fixedSubgroup_eq_comap_of_equivariant_mono` packages these
equivalences as equality of subgroup functors.

If `i` represents an `a`-stable subgroup functor `F`,
`onRepresentedSubgroup_fixedSubgroup_eq_comap` applies this comparison to
the published action `a.onRepresentedSubgroup i hi hF`, using its inclusion
equation. `onRepresentedSubgroup_restrict_fixedSubgroup_eq_comap` applies the
same argument after restriction along any homomorphism into the acting group.
Consequently, `onRepresentedSubgroup_restrict_fixedSubgroup_eq` transfers an
equality of restricted and ambient fixed functors to the action on `C`.

Suppose also that the ambient fixed functor is contained in `F`, and that
`z : Z ⟶ G` represents that fixed functor. `representedFixedFactor` factors
`z` through `i` using the published `IsRepresentedBy.factorHom`.
`representedFixedFactor_comp` states the factorization equation.
`onRepresentedSubgroup_isRepresentedBy_fixedFactor` proves that the resulting
map `Z ⟶ C` represents the fixed functor on `C`. Its monomorphism follows
from the monomorphism of `z`. For its range, an image of a `Z`-point maps
to an ambient fixed point. Conversely, a `C`-point whose image is ambient
fixed lifts through `z`; cancellation of `i` identifies the lift's image in
`C` with the original point. Finally,
`isClosedSubgroup_representedFixedFactor` proves that this factor is closed
when both `i` and `z` are closed, by the published closed-immersion
factorization lemma.

All assertions are derived from the imported definitions, equivariance,
representation on every test scheme, and monomorphism cancellation. They
introduce no external mathematical input. In the solvable fixed-containment
connectedness argument, they supply the comparison of fixed representatives;
they do not themselves assert connectedness.
