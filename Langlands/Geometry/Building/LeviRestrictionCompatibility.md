# Compatibility of a prescribed Levi restriction class

This internal helper module for Levi apartment-axiom inheritance identifies a supplied
restriction class with the constructed restriction, propagates the supplied
point pair across the class, and transfers full centralizer compatibility (V6)
to any centralizer representative of a standard Levi. It also gives the
semisimple case of a same-torus dynamic Levi inclusion.

`exists_leviRestriction_of_pair` translates the ambient point by the same real
cocharacter vector that takes the supplied Levi point to the requested point.
The proof uses `KPApartmentData.equipollent_of_mem`, `KPApartmentData.vadd_mem`
and `RootFunctionFamily.vadd_apply`. It needs no uniqueness theorem for
compatible apartment classes and no apartment-existence assertion.

`eq_leviRestrictedApartmentData_of_pair` applies to the general dynamic-centralizer
setting of `leviRestrictedApartmentData`. On the Levi roots the supplied pair
identifies its Levi valuation with `leviRestrictedRootFunctionFamily`; off those
roots both are infinity, by `IsRootDatumValuation.eq_top_of_not_mem_roots` and
`leviRestrictedRootFunctionFamily_apply_not_mem`. The resulting common member
identifies the full classes by `KPApartmentData.eq_of_common_mem`, from
`CrossTorusApartmentComparison`.

`isOmegaCompatible_standardLevi_of_pair` applies
`Langlands.Plancherel.RenardCartan.isOmegaCompatible_standardLevi_of_restriction`
from `RenardLeviCentralizerCompatibility` to the all-point restriction result,
then uses `KPApartmentData.IsOmegaCompatible.of_centralizerDatum` from
`LeviApartmentComparison`. The latter transfers V6 to the supplied representative
of the same actual centralizer.

`cocharacter_eq_zero_of_isSemisimple_levi` applies to any dynamic-centralizer
Levi `j : M → G` through which the same split closed torus factors. By
`relativeRoots_centralizer_factor`, every relative root of `M` annihilates the
defining cocharacter. If `M` is semisimple,
`IsSemisimple.cocharacter_eq_zero_of_annihilates_relativeRoots` from
`SemisimpleReflectionReduction` makes that cocharacter zero.
`exists_leviIso_of_isSemisimple` then rewrites its centralizer as the whole
ambient group by `groupHom_zero_comp_eq_trivialCocharacter` and
`Dynamic.centralizer_trivialCocharacter`. The representing inclusion is the
homomorphism of `SubgroupFunctor.IsRepresentedBy.topIso`, with its literal map
equality given by `topIso_hom`, from `CentralizerReductiveTransport`.
`isIso_leviHom_of_isSemisimple` records the resulting `IsIso j`.

The source interpretation is KP Section 6.7, Lemma 6.7.1 (2)–(3), and the
semisimple case discussed in the published target
`LeviApartmentAxiomsInheritanceStatement`. These helpers are derived from the
cited Library results; no new source assertion is used. They do not assume
`LeviApartmentRestrictionStatement`, building validity, or apartment availability.
