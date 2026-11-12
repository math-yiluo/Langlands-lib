# Opposite cones on the same actual Levi split component

Worker 135. This internal derived unit compares compatible root presentations
of two actual parabolics whose specified Levi embeddings agree and whose
rational-point intersection is exactly that common Levi. It introduces no
new transcription from the literature.

The ambient group is affine, smooth and locally of finite type over a field;
connected reductivity is supplied for actual maximal-split root negation.
Both presentations use the same actual split component `a : A → M`, but their
maximal split tori, generic cocharacters and simple-root subsets may differ.
The opposition hypothesis is only the equality of subgroup-functor carriers
at the ground-field identity test, not an assumed all-test intersection.

`neg_mem_componentRelativeRoots` descends the proved ambient root-negation
theorem through actual split-torus character restriction. The published
rational intersection root-sign theorem then proves
`opposite_componentRoot_signs`: on every actual root of `A` in the ambient
group, the second defining cocharacter is weakly positive exactly when the
first is weakly negative, and likewise for strict signs. The common Levi
identifies their dynamic centralizers, while the original parabolic images
identify the rational intersection in that theorem.

`neg_mem_intrinsicPositiveRoots_of_opposite` combines these strict signs with
root negation. Finally, `neg_mem_nonnegCone_of_opposite` writes a vector in the
second cone as its existing finite nonnegative restricted-root sum. Each
negated restricted root is an intrinsic positive root vector in the first
cone; nonnegative scalar multiplication and finite addition finish the proof.
`mem_nonnegCone_iff_neg_mem_of_opposite` applies this result in both directions;
commutativity of the rational intersection and the same-Levi equality discharge
the reversed hypotheses. Thus the second cone is exactly the negative of the first.
`oppositeNonnegConeEquiv` bundles this exact comparison as an equivalence
between the subtypes of vectors in the second and first cones. Both maps send
a vector to its negative; double negation proves both inverse laws. Its
construction depends on exactly the hypotheses of the comparison lemmas.
This unit supplies this concrete cone equivalence and its supporting lemmas;
existence of presentations and representation-theoretic regularity remain
separate results.
