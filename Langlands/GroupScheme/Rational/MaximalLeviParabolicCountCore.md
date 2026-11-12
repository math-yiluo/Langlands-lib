# The bound for parabolics with a common maximal Levi

`maximalLeviParabolicCount_core` proves the exact
`Langlands.GroupScheme.MaximalLeviParabolicCountStatement` over every field.
It is a derived structural count associated with Renard V.4.8, printed p.122 /
PDF p.128. The implementation uses the Library's actual subgroup functors and
root cones rather than a Weyl-coset classification.

The proof chooses a split component of the given Levi by
`splitComponentStatement`, and a compatible root presentation by
`parabolicRootPresentationExistence`. Properness of the original parabolic
implies that its Levi image is not the whole ambient group, by
`range_comp_ne_top_of_not_isIso`. The theorem
`ParabolicRootPresentation.restrictedRoots_nonempty` then supplies a restricted
simple root `x`. Its positive evaluation on the presenting split-component
cocharacter proves `x ≠ 0`. The root restriction identity
`latticePairing_restrict_eq_zero_of_isCentral` proves that `x` vanishes on
central cocharacters of the ambient group.

For every member of the family, the proof chooses a compatible root
presentation for the same split component and records whether its positive
cone contains `x`. If two cones both miss `x`, the published theorem
`maximalLeviConeComplement` identifies the two parabolic subgroup images.
If both contain `x`, pointedness
`ParabolicRootPresentation.notMem_positiveCone_or_neg_notMem` implies that both
miss `-x`; the same theorem again identifies their images. Each rational
Levi's defining radical-existence field supplies the radicals needed to apply
that theorem. The hypothesis that the original images are distinct therefore
makes the sign map into `Bool` injective. The finite cardinality bound is two.

The proof imports the published split-component, root-presentation and maximal
cone-complement proofs, and the pointed-cone lemma from
`MaximalLeviFixedDirectionNormalizer`. It assumes no root presentation,
central-annihilator vector, or auxiliary theorem. It does not prove the
geometric lemma, an orbit-to-parabolic injection, a Jacquet detection theorem,
or the represented induction length bound.
