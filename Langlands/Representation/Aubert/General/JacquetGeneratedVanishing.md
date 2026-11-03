# Jacquet vanishing from generating families and their subquotients

Author: Worker 593. The final subquotient step uses Worker 379's published
`jacquet_subsingleton_of_isSubquotient`.

This is an internal algebraic reduction for the full smooth support-vanishing
task. Its provenance is the universal property of the existing character
coinvariant quotient, followed by the published exactness consequence for actual
subquotients. It asserts no geometric lemma or support presentation.

`Langlands.Jacquet.Localization.subsingleton_coinvariants_of_iSup_range_eq_top`
works for a commutative coefficient ring, a group, an arbitrary subgroup `U` and
an arbitrary character of `U`. The target representation is generated as a
module by the images of a family of actual intertwiners. If the character
coinvariants of every source vanish, those of the target vanish. The family may
be infinite or empty. Its index universe, source-carrier universe and
target-carrier universe are independent.

The proof applies the existing `mapLinear` to each source quotient. The source
quotient is zero, so the target quotient map kills every intertwiner image.
Its kernel therefore contains the supremum of their ranges, which is the whole
target module by the stated generation hypothesis. Surjectivity of the quotient
map then proves that its target is a subsingleton. No smoothness, topology,
compactness, exactness or finite-length assertion enters this algebraic proof.

`coinvariantsEquivBotOfGeneratingFamily` turns that subsingleton proof into
an explicit linear equivalence from the coinvariants to the zero submodule
of the target carrier, using `LinearEquiv.ofSubsingleton`.

`Langlands.Aubert.General.jacquet_subsingleton_of_iSup_range_eq_top` specializes
this result to the literal carrier of the actual normalized Jacquet functor on
smooth complex representations. Its inverse half-Haar twist changes the action,
so its carrier is the character coinvariant quotient at the trivial character
already used by the algebraic result. The displayed semidirect decomposition,
closedness of `U`, local compactness and nonarchimedean group structure are those
needed to define the existing normalized functor. It adds no compact-limit
premise.

`jacquet_subsingleton_of_isSubquotient_of_iSup_range_eq_top` then applies
`jacquet_subsingleton_of_isSubquotient`. This last step explicitly requires
`Jacquet.Localization.IsLimitOfCompactSubgroups U`, as does that published
theorem. Its implementation uses
`jacquetFunctor_map_isShortExact` on invariant-submodule and quotient sequences.
The reduction imposes no finite-length or irreducibility condition on any
representation.

For a presentation as a sum, the canonical maps from the summands supply the
generating family. This formulation does not choose a direct-sum construction or
resize a family of representations. To use it for the exact
`RationalSupportCategoryJacquetVanishingStatement`, one still has to prove the
required presentation of each member of the actual support category and
vanishing for every presenting induced object. Neither assertion is a
conclusion of this file. The rational standard compact-limit premise can be
supplied separately by the published
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.

The proof bodies use no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem. Imports provide the
existing support framework and its subquotient reduction; they do not discharge
the remaining representation-theoretic inputs.
