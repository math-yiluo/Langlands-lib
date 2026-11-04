# Structural Levi criterion for a corrected filtration cell

Worker 1312. This internal derived construction separates the structural
conclusion of corrected graded vanishing from the remaining analytic argument.
For subsets `I`, `J` and a Weyl element `w`, write
`H = simpleImage cs w⁻¹ J ∩ I` and `K = simpleImage cs w I ∩ J`.
No representation-theoretic vanishing theorem is asserted by this pair.

`simpleImage_inv_inter_eq_iff_mapsIntoSimple`, in
`Langlands.Group.RelativeWeylIndexing`, proves `H = I` if and only if
`MapsIntoSimple cs w I J`. Both directions conjugate the same simple-reflection
equality by the inverse element. This holds without minimum-representative or
root-sign hypotheses, so it is a statement about reflection labels, not signed
root images. `simpleImage_inv_inter_ssubset` records `H ⊂ I` when `H ≠ I`.
`card_simpleImage_intersections` proves `H.card = K.card` by applying
`Fintype.card_congr` to the published `simpleConjugationEquiv`, instantiated
with `mapsIntoSimple_intersections` and `simpleImage_inv_inter`. This equality
also needs no minimum-representative or root-sign hypothesis.

The other declarations are in
`Langlands.Aubert.General.RationalPointFamily`.
`not_rootAssociation_of_card_lt` uses the published
`rootAssociation_card_eq`: association of `I` with a smaller finite index
contradicts equality of their cardinalities.
`not_rootAssociation_below_proper` applies this to a subset of a proper
subset of `I`. `correctedIntersection_supportExclusion` specializes that
fact to `H`. Its conclusion is the association and literal Levi-membership
exclusion occurring in
`SupportCategoryJacquetVanishingTarget`, with `H` as that target's containing
index. `correctedTargetIntersection_supportExclusion` supplies the same
antecedent with containing index `K`, since every subset `K' ⊆ K` satisfies
`K'.card ≤ K.card = H.card < I.card` when `H ≠ I`. In each case association
alone is impossible, so no separate Levi-membership argument is needed.
These laws supply the antecedents without assuming or proving the
support-category vanishing assertion. The target index `K` is the index of
the Jacquet module of the original representation in the one-cell term;
`H` is the corresponding induction index inside `M_I`.

For `hw : IsMinimal cs J I w` and `H = I`,
`correctedLeviConjugationMembership` proves, for every actual normalizer lift
`m` with `QuotientGroup.mk m = w⁻¹`,

`∀ x, x ∈ levi i ν I ↔ m⁻¹ * x * m ∈ levi i ν K`.

The proof uses `isMinimal_inv` and the published
`rootSet_simpleImage_intersections` at the swapped indices `J`, `I` and element
`w⁻¹`. This gives the actual character-set image `w⁻¹(K) = I`. The underlying
result uses `RootLengthComparison`, `PositiveSimpleReflectionComparison` and
the proved intrinsic minimum/length criterion, so the passage from reflection
labels to characters retains positivity. `weylCharacterAction_point_mk`
identifies the action with the same actual lift. The published
`levi_map_conj_of_character_image` and
`conjugationMembership_of_map_eq` then give the displayed membership
equivalence. The all-test `StandardLeviConjugationStatement` required by that
adapter is derived from the supplied `StandardCocharacterStatement` using
`standardLeviConjugationStatement_of_standardCocharacterStatement`; it is not
an additional input.

`exists_correctedLevi_of_full_intersection` chooses this literal `K` and
records `K ⊆ J`. Thus its conclusion is the structural conclusion of
`CorrectedGradedVanishingTarget` when `J = Finset.univ \ s`.
It still requires `H = I`; this equality is not deduced from a changing
filtration step here.

`correctedLeviConjugationEquiv` constructs the actual continuous group
equivalence from `levi i ν I` to `levi i ν K`, using the preceding literal
membership statement and the published `conjugationEquiv`. Its evaluation
theorem is definitional: the map is inverse conjugation by the specified `m`.
The topology can be any topological group topology on the actual rational
points, including the target's canonical evaluation topology.

The scope is arbitrary fields, a monomorphic torus map with the displayed
affineness instance, and the two point normalizer/centralizer comparisons.
The proper-subset association obstruction needs no finite enumeration of all
simple roots. The finite simple-image constructions assume a finite
enumeration of the actual simple-root subtype and a Coxeter system on the
actual normalizer modulo its full centralizer. The Levi-conjugation deductions
also require the two displayed root-sign comparisons, connected reductivity,
a maximal split torus, a generic cocharacter and the named standard-cocharacter
statement. Weyl finiteness, characteristic zero, splitness of the ambient group,
nonempty roots and hypotheses on representations are absent.

Provenance is internal composition of the named published declarations and
elementary finite-set and conjugation arguments. There is no use of
classification, character independence, adjointness or a geometric-lemma
representation identity. The localized comparison between the actual
corrected support restriction image and the appropriate Jacquet module,
full-smooth support-category vanishing, and the implication from a changing
actual filtration step to `H = I` remain proof obligations. Consequently this
pair does not prove `RationalCorrectedGradedVanishingStatement`.
