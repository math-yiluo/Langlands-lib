# Maximal-Levi containment from dynamic parabolic presentations

This internal reduction retains one geometric premise:
`ParabolicDynamicStatement.{u}`. The predicate
`MaximalLeviContainmentFromParabolicDynamic` is the implication from this
premise to the exact published `MaximalLeviContainmentStatement.{u}`.
The theorem `maximalLeviContainment_of_parabolicDynamic` proves this
implication. It does not prove the premise or the unconditional target.

The helper `exists_commonSplitComponentCocharacters_of_levi_le` begins with
actual rational Levis, two supplied dynamic presentations of their original
parabolics, and containment of their ambient Levi images. It produces a
split component of the smaller Levi and two cocharacters of that component
which realize the original parabolics and original Levi centralizers.

For the smaller Levi, the published `splitComponentStatement` and
`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
give the presentation. For the larger Levi,
`IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic`
supplies a presenting cocharacter. Its centralizer is its original Levi image
by `IsRationalLeviSubgroup.centralizer_eq_of_dynamicParabolic`.
The assumed Levi containment and symmetry of cocharacter commutation put this
cocharacter inside the smaller Levi. It is central there since that smaller
Levi centralizes it. The published `IsSplitComponent.exists_factor` therefore
factors it through the chosen split component. This argument preserves both
original parabolic maps.

For the reduction, `ParabolicDynamicStatement` first supplies dynamic
presentations of the two given rational parabolics. If their Levi inclusion
were strict, `exists_properCentralizerCoarsening` would construct a third
cocharacter on the common split component. Its parabolic contains the
original maximal parabolic, and its centralizer is strictly larger than the
original Levi while remaining proper. Properness of the second original
parabolic ensures its centralizer is proper, since a full centralizer has
full dynamic parabolic and a monomorphic full-range map is an isomorphism.

The affine representative of the new dynamic parabolic is an actual rational
parabolic by the reverse implication of the same retained premise. The
original parabolic factors through it. Maximality says that this factor map
or the new parabolic map is an isomorphism. In the first case, the original
Levi centralizer theorem forces the new centralizer to equal the original
Levi, contradicting strictness. In the second case, the new dynamic
parabolic is full. The published
`Dynamic.parabolic_eq_top_iff_centralizer_eq_top`, applied to the ambient
connected reductive group, forces its centralizer to be full, contradicting
properness.

The reduction is derived entirely from the named published proofs and the
finite-weight lemmas in this development. No external literature assertion,
relative-root-system classification, rank formula, root-negation assertion,
or additional geometric unipotent-radical premise is used. An actual proof of
`ParabolicDynamicStatement` is still required before this implication can
yield the task's unconditional theorem.

The existing helpers `isIso_of_full_range`, `full_range_of_isIso` are public so related modules can reuse their unchanged proofs.
