# Restricting a semidirect decomposition to an intermediate subgroup

This internal construction starts from the published actual-subgroup predicate
`IsSemidirectDecomposition P M U` and inclusions `U ≤ Q ≤ P`. It proves the
inherited decomposition `Q = (M ⊓ Q) ⋉ U`. The existing projection preserves
`Q`; its value and the remaining radical factor give existence of the
decomposition, and `projection_eq_iff` proves uniqueness.

The inherited projection agrees with the original projection on underlying
elements. Its continuity follows by restricting the original continuous
projection and viewing its value in the subgroup `M ⊓ Q`. This step requires
only a topological space on the ambient group.

`restrictedCoordinates` packages multiplication in the inherited factors as a
homeomorphism `(M ⊓ Q) × U ≃ₜ Q`, using the published continuous
semidirect coordinates and the restricted continuous projection.

These are derived group and topology facts. No additional reductive-group or
representation-theoretic input is assumed.

For a locally compact topological ambient group with second-countable topology,
`closedNormalizerCharacter_eq_mul` applies the published product-Haar theorem
to simultaneous conjugations on three closed subgroups. Conjugation respects
the multiplication coordinates, so its positive normalizer character is the
product of the characters on the two factors.

Finally, `closedNormalizerCharacter_subgroupOf_of_mem` compares the same closed
subgroup `W ≤ M` read in the full group and inside the closed subgroup `M`.
The canonical continuous multiplicative equivalence conjugates the two
automorphisms. The published invariance of `mulEquivHaarChar` under transport
then identifies their scaling factors. This transport step does not require
second countability.

The `_of_mem` name distinguishes this version, which accepts an explicit
normalizer-membership proof inside `M`, from the published
`closedNormalizerCharacter_subgroupOf` in `SubgroupOfModulus`, which derives
that membership. Both retain their original hypotheses and conclusions.
