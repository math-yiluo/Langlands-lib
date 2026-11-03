# Actual rational normalized induction in stages

Author: Worker 438.

This is an internal specialization of `normalizedInductionStagesIso` from
[`InductionStages`](InductionStages.md) to the literal rational standard
subgroups. It uses the subgroup geometry and the positive Haar character
calculation already proved in
[`RationalInductionStagesGeometry`](RationalInductionStagesGeometry.md) and
[`RationalHaarModulus`](RationalHaarModulus.md). It supplies no new external
literature assertion. The final Aubert compatibility equation on the exact
finite-length Grothendieck group remains a separate obligation.

The setting is a connected reductive group scheme `G` over an arbitrary
nonarchimedean local field `k : Type u`, a maximal split torus `i`, and a
generic cocharacter `ν`. The hypotheses retain
`StandardLeviIntersectionStatement` and `StandardCocharacterStatement`, the
canonical `pointTopology` on `RationalPoint k G.X`, local compactness and the
nonarchimedean group structure, closedness of every standard radical,
continuity of the actual standard projections, and the compact-subgroup-limit
condition for every standard radical.

For every `J : Finset (SimpleRoot i ν)` and `I : Finset J`,
`standardInductionStagesIso` is the natural isomorphism from normalized
induction from the fine Levi to the coarse Levi `levi i ν J`, followed by
normalized induction from that coarse Levi to `G`, to direct normalized
induction through `parabolic i ν (leviIndex J I)`. Its fine-to-coarse functor
is exactly `leviNormalizedInductionFunctor`, including the canonical pullback
between the actual fine Levi and its literal subgroup copy inside the coarse
Levi. Input and output coefficient carriers have the target universe
`Type (max (u + 1) v)`, with independent `u` and `v`.

This form takes closedness of the actual coarse Levi and the compact-limit
condition for the inner radical as explicit premises. It retains all finite
subsets, including the empty and full cases. It assumes neither an isomorphism
of functors nor a positive modulus identity. The construction instantiates the
generic stages isomorphism with the two standard semidirect decompositions
and the published literal decomposition inside the coarse Levi. The
required subgroup inclusions come from `levi_le_of_subset`,
`parabolic_le_of_subset`, and `unipotent_le_of_subset`.
`standardJacquetModulus_stages` supplies the exact positive modulus equality;
`inductionStagesInnerModulus` is definitionally the rational
`standardInnerJacquetModulus` at these parameters. Thus both half-character
normalizations and the natural inverse maps are inherited from the generic
construction.

`standardInductionStagesIso_of_premises` additionally assumes that the rational
point group is Hausdorff and all standard parabolics are closed. It derives
closedness of the actual coarse Levi by `levi_isClosed` and obtains the
inner compact-limit condition by
`isLimitOfCompactSubgroups_leviUnipotent`. These are exactly the earlier
closedness and restriction deductions in
[`RationalInvolutivityReduction`](RationalInvolutivityReduction.md).
No inside-Levi projection-continuity, admissibility, finite-length, geometric
lemma, or classification assumption is used by either construction.
