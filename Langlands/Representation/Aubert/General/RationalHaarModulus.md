# Haar modulus for the actual rational standard family

This internal prerequisite derives second countability for finite-type affine
rational points with the exact published evaluation topology. It transports
through `rationalPointHomeomorph` and `affinePointsRingPointHomeomorph` to the
published second-countable affine group-point space. For a connected reductive
group over a nonarchimedean local field, smoothness supplies finite type locally,
and the existing local-field theorem supplies second countability of the field.
No new assumption is added to the rational Aubert target.

`standardUnipotentStagesCoordinates` applies the inherited decomposition to the
fine radical inside the coarse parabolic. The root-intersection statement
supplies the two required inclusions, and the given continuous coarse
projection supplies continuity. Multiplication identifies the actual fine
radical with the product of its intersection with the coarse Levi and the
coarse radical.

`standardJacquetModulus_stages` applies the product-Haar character theorem to
conjugation by each fine Levi point. Both radicals and the coarse Levi are
closed by the target's existing premises, and rational-point second
countability was derived above. The fine Levi normalizes both factors. The
subgroupOf modulus transport identifies the intersection factor with the exact
`standardInnerJacquetModulus` used for Jacquet stages. Commutativity of positive
scalars gives coarse times inner equals fine. No additional modulus identity
is assumed. A private lemma first performs the character calculation for an
arbitrary topological group; the rational theorem specializes that lemma.
Equality of the two inside-Levi radical subgroups is handled by substitution
before comparing their normalizer characters.

The subgroup modulus comparison uses
`closedNormalizerCharacter_subgroupOf_of_mem` from `SemidirectRestriction`,
which accepts the explicitly supplied inside-normalizer proof.
