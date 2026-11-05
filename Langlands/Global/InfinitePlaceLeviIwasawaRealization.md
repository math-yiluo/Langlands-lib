# Actual archimedean Levi-compatible Iwasawa assembly from realization

Author: Worker 1655.

This internal derived adapter applies the compatible diagonal polar construction
to the actual infinite-place completion in arbitrary universe `u`. It proves all
four conclusions on the original point groups once compatible realization on the
completion pullback is supplied. It does not prove that realization exists for
every rational pair.

`HasCompletionDiagonalStarLeviRealization` uses the published
`NumberField.InfinitePlace.completion_isRCLikeNormedField` and
`IsRCLikeNormedField.rclike` to install an analytic structure on `v.Completion`.
This structure retains the existing normed field structure, including the
completion topology. The predicate then asks for
`Dynamic.HasDiagonalStarLeviRealization` for the actual base change of `p` and
the composite of the actual base changes of `l` and `p`. Its input data consist
of a closed representation with star-stable point image and one diagonal
cocharacter representing the specified parabolic and Levi subgroup functors.
The predicate supplies no compact subgroup or decomposition.

`exists_leviCompatibleIwasawaCompact_of_completion_realization` first obtains
affineness of the original ambient group and specified Levi from their
connected reductivity. The diagonal polar theorem then constructs a compact on
the actual completion pullback and proves ambient maximality, the ordered
parabolic range product, the literal parabolic/Levi intersection equality, and
maximal compactness of the inverse image on the actual Levi point carrier.
The existing completion base-change equivalence transfers all four conclusions
back to `InfinitePlaceGroupPoints F G v`. It compares both the ambient and Levi
carriers by multiplicative homeomorphisms in their regular-function evaluation
topologies; the Levi homomorphism is induced by the original composite `l ≫ p`.
No topology identification or Levi base-change theorem is an extra premise.
The pointwise theorem needs no separate parabolicity assumption because the
realization predicate already contains representation of its dynamic parabolic.

`CompletionDiagonalStarLeviRealizationStatement` universally quantifies this
remaining obligation over precisely the fields, groups, rational parabolic/Levi
pairs and infinite places of `LeviCompatibleIwasawaStatement`, including its
arbitrary universe. The final theorem proves that this realization statement
implies the exact existing Iwasawa proposition by applying the pointwise
adapter to each pair. The hypothesis remains unproved. In particular this is
not an unconditional proof of `LeviCompatibleIwasawaStatement` and does not
complete the host task.

The provenance is internal composition of the published compatible completion
analytic structure, actual-point base-change transport and the conditional
diagonal polar construction. No external structural existence theorem is
asserted here.
