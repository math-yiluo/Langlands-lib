# Existence of rational parabolic galleries

These are internal geometric targets for the persistence argument in
Task 5515. Neither target is proved in this module.

`RationalParabolicGalleryStatement` asserts that any two actual rational
parabolic subgroup functors of a connected reductive group over any field,
with the same specified embedded rational Levi, admit a finite rank-one
gallery as defined in `ParabolicGallery`.

`RationalParabolicGalleryAvoidingStatement` specifies a central split
subtorus `B` of the original Levi `L`. If the endpoint parabolics have the
same intersection with `Z_G(B)` as subgroup functors on all scheme tests,
there is a finite gallery all of whose intermediate rank-one Levis have
noncentral `B`. The endpoint hypothesis says exactly that the two
parabolics agree on the roots vanishing on `B`. The output is the
noncentrality predicate in `ParabolicGallery`, not an assumed equivalence
with a numerical rank or a particular root datum. The conjunction
`RationalParabolicGalleryStatements` collects the two targets.

The expected application takes `B = A_M`, `L` a cuspidal-support Levi
inside `M`, and endpoints `QN` and `QNbar`. Their intersections with
`Z_G(A_M) = M` are both `Q`. This application also needs the existing
centralizer and nested-parabolic comparisons; none is asserted by this
statement pair itself.

The targets are derived geometric assertions. A proof can select defining
cocharacters in the split component of `L`, identify their chambers using
the finite relative roots, and perturb a straight path so that it crosses
only one root hyperplane at a time. The endpoint agreement allows the path
to remain in one chamber for the roots vanishing on `B`. Dynamic
parabolics at each crossing give the actual intermediate parabolic and
Levi, and the exact inner intersections give opposite maximal proper
parabolics. The intended inputs are the published actual dynamic,
root-presentation and nested-decomposition results. This rationale
explains the provenance of the internal targets, without claiming their
Lean proofs have been implemented.
