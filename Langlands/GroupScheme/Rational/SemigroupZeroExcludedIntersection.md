# Zero-excluded semigroup intersections

This derived supporting unit proves the actual semigroup inverse-image equality
under an equivariant closed inclusion when the additive semigroup excludes zero.
The two independent source inputs remain explicit:
`SemigroupRealizationStatement` and
`CoordinateWeights.AugmentationLieContainmentStatement`. Their conjunction is
named `SemigroupZeroExcludedIntersectionPrerequisites`. This file does not
supply proofs of either input or of the full host comparison statement.

All groups are actual smooth affine group schemes over an arbitrary field, all
actions and equivariance identities use every test scheme, and character
weights use the all-coefficient-algebra convention. The acting group is a split
torus. The theorem does not require connectedness of the closed subgroup `H`.
This is a derived argument using published coordinate-weight quotient and
actual tangent-image results, together with the supporting identity-component
and intersection geometry modules. It is not a transcription of a source
proof.

`CoordinateWeights.support_subset_of_closedImmersion` applies the actual pointed
affine closed-immersion theorem to the two group actions after forgetting their
group laws. The existing theorem lifts augmentation eigenfunctions weight by
weight, so the augmentation support of the source is contained in that of the
target. `trivialInvariantAugmentation_of_closedImmersion` consequently passes
absence of zero augmentation weight to any equivariant closed subgroup.

`trivialInvariantAugmentation_semigroup_representative` concerns a smooth
connected affine representative `L` of the ambient semigroup subgroup, with the
induced actual action. Its intrinsic tangent support is precisely the ambient
support of the represented subgroup. The given exact semigroup Lie image and
independence of split-torus weight spaces therefore bound that support by the
semigroup `A`. The coordinate/Lie containment input transfers this bound to the
augmentation support of `L`. Since zero is absent from `A`, its augmentation
has no zero weight.

For `semigroup_comap_eq_of_zero_not_mem`, choose such a representative `L` by
semigroup realization and form the actual pullback `K = H ×_G L`. Its first
projection represents the inverse-image subgroup on every test scheme. The
previous intersection geometry gives smoothness of `K`. Its second projection
to `L` is a closed immersion because `H → G` is one. Pullback compatibility and
cancellation against the representing monomorphism prove that this second
projection intertwines the two induced actions. The coordinate quotient result
then excludes zero from the augmentation support of `K`.

`connectedSpace_of_trivialInvariantAugmentation` proves `K` connected. The
previous exact Lie-image and connected-representative equality theorem now
identifies the full inverse-image subgroup functor with the semigroup subgroup
of `H`. The implementation proves equality on every test, including nonreduced
tests, rather than equality merely on field-valued points.

The coordinate and realization inputs, the zero-containing solvable and normal
intersection alternatives, general functoriality and the smooth quotient
comparison remain outside this unit's conclusion.
