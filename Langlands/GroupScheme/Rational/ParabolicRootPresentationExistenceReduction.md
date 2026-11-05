# Presentations from simultaneous dynamic realization of specified maps

Authors: Worker 1294.

This is an internal supporting reduction for the exact published parabolic-root
presentation target. It does not prove general presentation existence. The
unproved `GenericMinimalParabolicStatement` and
`RelativeRootNegationStatement` remain explicit inputs, as does a cocharacter
simultaneously realizing the specified parabolic and Levi images.

`IsSplitTorus.exists_genericCocharacter_refining` chooses a generic cocharacter
and applies the finite integral perturbation theorem to all actual relative
roots. A sufficiently large positive multiple of the original direction plus
the generic direction stays generic and introduces no new nonnegative root
pairings. This is unconditional for split-torus maps into affine groups locally
of finite type.

`exists_generic_standardFace_realizing` uses the published root-sign inclusion
criterion to deduce dynamic-parabolic containment. The original cocharacter is
standard for its zero face among the simple roots of the generic refinement.
Genericity and the explicit negation-stability premise show that every standard
cocharacter for that face has the same signs on all relative roots. The published
sign-to-dynamic comparison identifies both the parabolic and centralizer, and
the defining intersections give the standard parabolic and Levi equalities.
This route requires no full root-system classification or reflection theorem.

`nonempty_parabolicRootPresentation_of_dynamic_realization` factors the supplied
simultaneous cocharacter through an actual maximal split torus and applies the
preceding refinement. The whole torus lies in the specified Levi centralizer.
The supplied central split component factors through that torus by ambient
maximality. These are the original maps throughout, with no replacement Levi.
The explicit generic-minimality premise supplies minimality; the refinement
supplies containment in the original parabolic. The original cocharacter is the
single witness realizing both specified images.

`parabolicRootPresentationOfDynamicRealization` chooses the resulting actual
presentation from this nonemptiness theorem. Its arguments retain the two
structural premises, the original parabolic, Levi and component morphisms, and
the single cocharacter together with both image equalities. The choice adds no
existence assertion beyond the preceding theorem.

`nonempty_parabolicRootPresentation_iff_dynamic_realization` gives the converse
as well: a compatible presentation already contains a cocharacter realizing the
two images. Under the same two explicit root premises this yields a fixed-map
equivalence. `parabolicRootPresentationExistenceStatement_iff_dynamic_realization`
quantifies that equivalence over exactly the field, connected reductive group
and specified maps of the published existence target. Its right side keeps
the parabolic, rational Levi and split-component hypotheses and asks for one
ambient cocharacter realizing both supplied images. This is a reduction, not
a proof of that remaining universal realization assertion.

The mathematical provenance is derived from the existing Library constructions
and their cited sources. The source motivation remains Renard 2026 V.3.9 and
V.3.14–V.3.15, printed pp.112–113/PDF pp.118–119. No new literal source assertion
or unconditional general existence claim is made. All fields and arbitrary
test schemes, including nonreduced tests and rank zero, are retained.
