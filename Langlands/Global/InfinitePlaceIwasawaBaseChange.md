# Actual completion base change for parabolic Iwasawa decomposition

Author: Worker 1359.

This internal derived construction transfers compact Iwasawa existence
between the original completion-valued group points and the completion-rational
points of the actual base-changed group scheme. It supplies comparisons and
algebraic preservation results, and does not prove Iwasawa existence.

`Langlands.CompactIwasawa.HasDecomposition f` records exactly the existence
of a subgroup `K` whose underlying set is compact, which is maximal among
all compact subgroups, and for which `Set.range f * (K : Set _) = Set.univ`.
The image of `f` is the left factor. The definition uses arbitrary groups
and topologies, in independent universes, without a supplied compact.

`HasDecomposition.transport` maps a witness subgroup by a multiplicative
homeomorphism `eG`, using a commuting multiplicative equivalence `eP` on
the source of the homomorphism. Compactness follows from continuity.
For maximality, pull any larger compact subgroup back along `eG`,
apply the original maximality, and map that equality forward. The product
covering is proved pointwise: decompose `eG.symm y` and apply the commuting
square and multiplicativity to its two factors. `hasDecomposition_iff`
applies this argument in both directions. No topological group assumption
or closedness premise is added.

`affinePointsBaseChangeMulEquiv_symm_target` proves naturality of the
published actual point comparison under every group-scheme homomorphism.
Both sides have the same underlying scheme map: compose a point with
the first projection of the actual pullback and the original homomorphism.
The pullback naturality identity proves equality. The forward naturality
theorem follows by injectivity of the inverse comparison. Neither
naturality identity requires the source or target to be affine.

For `F : Type u`, an infinite place `v`, and an actual group scheme `G/F`,
`completionBaseChange F G v` is literally the existing group-scheme
pullback along `Spec.algebraMap F v.Completion`. For affine `G`,
`completionBaseChangeHomeomorph F G v` specializes the published
`affinePointsBaseChangeContinuousMulEquiv` to `C = F` and
`D = A = v.Completion`. Its source is precisely the Library's
`InfinitePlaceGroupPoints F G v`, and its target is the actual rational
point group of the pullback over `v.Completion`. Both topologies are
the existing global regular-function evaluation topologies.

`hasDecomposition_completionBaseChange_iff` combines this homeomorphism
with the actual multiplicative comparison on `P` and the naturality
identity. It therefore preserves all three exact compact Iwasawa
conclusions and the literal parabolic point-map range. It requires
affineness of the ambient group only; no parabolic premise is needed
for the comparison itself.

Finally, `isConnectedReductive_completionBaseChange` and
`isParabolicSubgroup_completionBaseChange` specialize the published
unconditional field-extension proofs. They establish the original
algebraic predicates on these actual pullbacks at every infinite place,
without splitness, properness or a number-field restriction beyond the
existence of the place. Every construction retains arbitrary universe `u`.

The provenance is the pullback-adjunction point comparison, its published
evaluation-topology homeomorphism in `AffinePointBaseChangeSmooth`, the
unconditional proofs in `Reductive.FieldExtensionProof` and
`Absolute.ParabolicFieldExtensionProof`, and elementary subgroup and
compactness transport. This file adds no external literature claim.
The general archimedean reductive-group compact existence and parabolic
covering theorem remains necessary to prove the published
`InfinitePlaceGroupPoints.ParabolicIwasawaStatement`.
