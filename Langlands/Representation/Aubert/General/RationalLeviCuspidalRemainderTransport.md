# Actual cuspidal remainder splittings on a standard rational Levi

Authors: Workers 1553 and 321. This is an internal conditional component of
the rational cuspidal Jacquet-factor extraction task.

`HasLeviCuspidalRemainderSplitting` is the local binary-coproduct condition
for exactly the proper inside-Levi standard tests used by `IsLeviCuspidal`.
Its ambient object is an actual smooth representation of the literal
closed subgroup `M I`. The true component is cuspidal; the false component
has no nonzero cuspidal actual subquotient. It asserts no splitting
existence.

`HasCuspidalRemainderSplitting.of_iso` composes both legs of the given
cofan with an actual ambient isomorphism and transports its colimit
witness. `hasCuspidalRemainderSplitting_pullback_iff` uses
`SmoothRep.pullbackEquivalence` to reflect as well as preserve splittings
under a supplied all-object cuspidality equivalence. Reflection pulls the
splitting back along the inverse group homeomorphism. The counit transfers
the cuspidality comparison to that inverse, and the unit identifies the
resulting ambient object with the original one.

For a connected reductive group over a topological field, take an actual
maximal split torus, a generic cocharacter, and an arbitrary finite subset
`I` of its actual simple roots. The intrinsic group is the published
`Standard.leviScheme` with its canonical `standardLeviTorusFactor`; the
other group is the literal rational-point subgroup `levi i ν I`. Both
scheme point groups use `pointTopology`.

`hasLeviCuspidalRemainderSplitting_iff_pullback` identifies their splitting
conditions through the actual `leviRationalPointHomeomorph`.
`rationalLeviCuspidalityTransport` supplies the complete cuspidality
comparison, with its exact matching of all proper root subsets and all
normalized Jacquet tests. The theorem retains the dynamic Lie and standard
cocharacter statements, connected reductivity of the actual Levi,
local compactness and nonarchimedeanness of both point groups, a finite
enumeration of the intrinsic simple roots, closed unipotent subgroups,
closedness of the literal Levi, and arbitrary legal intrinsic and inner
semidirect decompositions. The field and representation universes are
independent.

`hasLeviCuspidalRemainderSplitting_of_rationalWholeCoproduct` consumes the
existing `Renard.EveryObjectIsCoproductOfComponents` condition for
`rationalWholeCuspidalDecompositionProperties` on the intrinsic group.
The published local adapter supplies its actual splitting, and the
comparison reflects it to the literal subgroup. This works for every
actual ambient representation; it needs no isomorphism comparing two
induction constructions.

Over any nonarchimedean local field,
`no_leviCuspidal_subquotient_of_proper_induction_rationalWholeCoproduct`
applies that splitting to actual normalized proper standard induction
inside the literal Levi. The published
`isUnimodularModulus_standardUnipotent_in_levi` discharges exactly the
unimodularity premise of
`no_leviCuspidal_subquotient_of_proper_induction_splitting`.
The conclusion excludes every nonzero cuspidal actual subquotient,
without irreducibility, finite length, admissibility or finite
generation hypotheses on either the inducing object or the tested
subquotient. The coproduct input is at carrier universe `max u v`,
matching the actual induction carrier.

The proof route is an internal deduction from the actual pullback
equivalence, cuspidality transport, supplied coproduct and conditional
proper-induction exclusion. The only adjointness use is transitive through
`no_cuspidal_subquotient_of_induction_splitting`, which uses the actual
`FirstAdjointness.equiv` under unimodularity. No classification theorem or
geometric-lemma conclusion supplies a step of these new proofs.

The intrinsic whole coproduct and connected reductivity of the actual
Levi remain inputs. A finite enumeration alone does not supply the
intrinsic `HasRelativeRootSystem` needed to apply the universal
`RationalWholeCuspidalCategoryDecompositionStatement`. This component
neither proves that universal statement nor constructs the actual
geometric filtration or proves the full
`RationalCuspidalJacquetFactorExtractionStatement`. Empty root systems and
empty selected subsets are included; the proper-induction conclusion
applies only when the displayed proper subset exists.

Worker 1751's naming repair assigns explicit module-specific names to the local instances in this file. This prevents generated-name collisions when the rebuilt inertia and norm-kernel branches are imported or replayed together. Only the instance names change; their values, topology, mathematical statements and proof bodies are unchanged.
