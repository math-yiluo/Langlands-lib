# Root points and the actual derived cover

This is an internal derivation from the Library's actual apartment axioms,
relative root subgroup functors, derived subgroup and central-isogeny
constructions. The field is an arbitrary-universe nonarchimedean local field.
The torus inclusion is a monomorphism, the ambient group is affine, the torus
is split, and the apartment satisfies `SatisfiesApartmentAxioms` for the actual
centralizer datum.

For each actual relative root `a`, `exists_positive_derived_cocharacter`
constructs a cocharacter with positive integer pairing with `a` whose full
image, on every test scheme, lies in the actual derived subgroup. The apartment
axioms give an affine root with derivative equal to the root form, a coroot
vector, and an actual normalizer point representing its affine reflection.
Its linear action negates evaluation of the root on the translation space.
Starting from a split-torus cocharacter `ν` with positive root pairing, the
negative of its composite with the torus commutator endomorphism has twice
that pairing. Its full image lies in the derived subgroup by the actual torus
commutator formula. No separate root-reflection existence hypothesis is used.

`positiveDerivedCocharacter` chooses this cocharacter; the two following
lemmas retain its positive pairing and all-test containment. For a supplied
actual derived inclusion `d : D → G`, `derivedContractingCocharacter` factors
its ambient composite through `D` using represented subgroup factorization.
`derivedContractingCocharacter_comp` identifies the exact composite with `d`.

Given a supplied `IsSimplyConnectedDerivedCover d π`, every rational point
of the actual relative root subgroup lifts through `π ≫ d`, as proved by
`exists_rootPoint_cover_lift`. The full root subgroup lies in the derived
subgroup, so its point has a unique derived-group preimage. The positive
cocharacter contracts the point in `G`. The closed-subgroup comparison for
dynamic subgroups transports contraction to the constructed cocharacter in
`D`. The semisimple covering source and target are affine, hence separated,
so `Dynamic.centralIsogenyLift` provides a rational cover point. Its composite
with `π ≫ d` is the original point. `rootPointCoverLift` chooses such an
actual point and `rootPointCoverLift_comp` retains the exact composite.
No rational surjectivity for arbitrary ambient points or all-test cover
lifting is asserted.

For the supplied `ParahoricBuildingData`, the existing maximal split torus
and simply connected derived cover meet these hypotheses. Thus
`rootGroup_le_simplyConnectedImage` proves its root-group containment
predicate under precisely the apartment premise.
`sharpFixer_le_simplyConnectedImage` applies the existing generated-subgroup
argument to every subset of the apartment, including the empty set.
`parahoric_le_zeroSubgroup` then uses the unchanged join definition: the
centralizer-zero factor lies in the zero subgroup by definition and the sharp
factor lies in its simply connected image. No nonemptiness or chamber
hypothesis is required for these containments.

These are intermediate results for the apartment-only affine Iwahori–Tits
theorem. They prove its parahoric containment obligation; normalities, the
actual affine-action comparison, the Tits axioms and saturation remain separate
obligations.
