# The actual rational target map in the literal Levi family

This internal adapter specializes `TargetInductionReduction` to the actual
rational standard family and the target intersections derived in
`RationalTargetInduction`. It retains the structural inputs of that module:
the point normalizer and full-centralizer comparisons, the supplied Coxeter
system, both all-test twisted-intersection properties, and the standard Levi
intersection statement. It works at every minimum point Weyl representative
and every normalizer lift, with the original finite simple-root labels.

The canonical rational-point topology is `pointTopology`. Under local
compactness, nonarchimedeanness and Hausdorffness of the rational-point group,
closedness of the actual standard Levis, radicals and parabolics, continuity
of the literal restricted projections inside `L_I`, and finite-length
preservation of the literal restricted normalized induction,
`pointTargetInductionPreservation` derives both finite-length and short-exact
preservation for the actual target induction. The private helper derives
restricted short-exactness from `normalizedInductionFunctor_preservesShortExact`
and compact open cofinality inside the closed Levi. The proof then applies
the generic target reduction using the already derived target Levi,
parabolic and radical identities. Preservation of the actual target functor
is not a premise.

`pointTargetInductionK0` constructs the resulting map on the full exact
finite-length Grothendieck group, using the actual target functor and both
derived preservation witnesses. The representation carriers retain the
independent-universe scope `max (u + 1) v`.

`pointTargetInductionK0_eq` identifies the complete map with literal
restricted `inductionK0` inside `L_I` at
`intersectionLeviIndex pointCs J I w⁻¹`. The rightmost factor identifies
the actual target-intersection Levi with the ambient standard Levi by
identity conjugation. Pullback along its canonical `subgroupOfContinuousEquiv`
then gives the inducing representation on the literal subgroup inside `L_I`,
followed by normalized induction. The proof rewrites the parabolic and radical
labels using `leviIndex_intersectionLeviIndex` and applies the generic full-map
comparison. The equality holds on all virtual classes and retains the actual
closed-subgroup Haar normalization.

The provenance is internal through the two named target adapters and the
published exactness and exact K0 constructions. The additional topological,
projection and finite-length premises are the literal inside-Levi premises
already displayed by the final rational induction target. This unit does not
establish its retained structural properties, normalized stages, Weyl
conjugacy, geometric expansion or the full rational Aubert compatibility
equation, and adds no premise to that final proposition.
