# Inside-Levi induction finite length

Author: Worker 1343.

This internal adapter derives finite-length preservation of actual
normalized induction inside a closed standard Levi from the ambient
normalized-induction finite-length hypotheses. It does not add a
normalized-stages premise or require an equality of three Haar moduli.

For the generic theorems, take semidirect decompositions
`P₀ = M₀ U₀`, `P₁ = M₁ U₁`, and the literal restricted decomposition
`P₀ ∩ M₁ = (M₀ ∩ M₁)(U₀ ∩ M₁)`, with `P₀ ≤ P₁`, `M₀ ≤ M₁`
and `U₁ ≤ U₀`. The ambient group is locally compact and nonarchimedean,
`U₀` is closed and unimodular in the modulus sense, the projection of
`P₁` onto `M₁` is continuous, and ambient normalized induction along
`P₀` preserves finite length. Group and representation universes are
independent.

`isFiniteLength_ordinaryInduction_in_levi` proves that ordinary induction
inside `M₁` of a finite-length smooth representation `A` of
`M₀.subgroupOf M₁` has finite length:

1. Pull `A` back along the inverse of `subgroupOfContinuousEquiv hM`.
   `SmoothRep.pullbackFunctor_preservesFiniteLength` gives a finite-length
   representation `B` of `M₀`.
2. `isFiniteLength_ordinaryInduction` applies ambient preservation to an
   inverse half-character twist of `B`. The normalization cancels, so the
   ordinary ambient induction has finite length.
3. `ordinaryStagesInflationEquiv` identifies this representation with
   outer ordinary induction of the inside ordinary induction, inflated
   along the actual projection `P₁ → M₁`. Transport length through this
   equivalence.
4. `Induction.isFiniteLength_of_smoothInduced` reflects finite length to
   the inflated coefficient representation. Its smoothness follows from
   continuity of the projection and `Induction.smoothInduced_smooth`.
5. The projection is surjective by `projection_levi`.
   `FiniteLengthAssembly.finiteLength_comp_surjective_iff` removes the
   inflation. The two opposite pullbacks of `A` cancel, identifying the
   inside coefficient action with `A.representation`.

`normalizedInduction_in_levi_preservesFiniteLength` additionally assumes
local compactness of `M₁` and closedness and unimodularity of
`U₀.subgroupOf M₁`. Twist `A` by the inside Levi half-character. This
preserves finite length by `finiteLength_twist_iff`.
`closedHalfCharacter_eq_comp_projection` identifies its inflation with
the normalized inducing action, so the ordinary result applies.

`RationalPointFamily.standardLeviInduction_preservesFiniteLength`
specializes this argument to the actual rational-point family. For
`I : Finset J`, put `I' = leviIndex J I`. The published
`parabolic_le_of_subset`, `levi_le_of_subset` and
`unipotent_le_of_subset` give the required containments from the named
standard-cocharacter and intersection statements. Ambient closedness,
projection continuity and induction preservation are the displayed
premises. Closedness of `levi i ν J` gives its locally compact structure.
`standardLeviUnipotent_isLimitOfCompactSubgroups` restricts the ambient
compact-limit premise, and
`isUnimodularModulus_of_isLimitOfCompactSubgroups` supplies both
unimodularity premises. The result has exactly the form of `hiLFl J` in
the rational induction-compatibility target, with canonical
`pointTopology` and representation universe `max (u + 1) v`. It includes
empty subsets and empty simple-root types.

Provenance is internal: the proof is derived from the actual representation
constructions and the displayed preservation premises. It uses neither a
geometric lemma nor classification, character independence, adjointness
or cuspidal support. The two
`FiniteLengthAssembly` declarations just used are generic algebraic
transport lemmas in `Classification/FiniteLengthProof`; their proofs use
subrepresentation lattices and surjective linear maps, not classification.
Specifically, `finiteLength_comp_surjective_iff` uses
`FiniteLengthAssembly.length_comp_surjective`, whose invariant-subspace
comparison is the generic
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`. The latter
identifies the same invariant subspaces under a surjective change of
acting monoid; it is not a cuspidal-support theorem.
This module proves no unconditional ambient preservation theorem and no
Aubert operator identity.
