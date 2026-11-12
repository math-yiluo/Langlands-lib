# Comparing a restricted Levi apartment with a prescribed compatible class

This internal adapter compares the restriction of an ambient apartment with a
supplied standard-Levi apartment at the same torus. It is supporting work for
the available-special-Levi target and supplies no final proof of that target.

`CentralizerDatum.comparisonIso` uses
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` to compare any two
representatives of the same actual torus centralizer. Its compatibility with
the ambient inclusions implies compatibility with the torus maps.
`comparisonIso_translation` then uses character restriction, the defining
evaluation identity of `centralizerTranslation`, and
`rationalCharacterValuation_characterRestrict` to prove that the actual
translation vector in the unchanged torus space is preserved.

`KPApartmentData.IsOmegaCompatible.of_centralizerDatum` transfers the full V6
identity through that comparison. Every point of the target centralizer
lifts through the isomorphism. The original ambient conjugating point and
translation vector are unchanged, so the original V6 identity applies.
The companion equivalence states independence of the representative.

`standardLevi_isConnectedReductive` applies the published
`standardCocharacter` proof to present the actual standard Levi as a
cocharacter centralizer, then applies the published
`dynamicCentralizerReductive` proof.

`exists_leviRestriction_of_omegaCompatible` has the still-unproved
`LeviApartmentRestrictionStatement` as an explicit premise. It takes the
restricted class and its surjectivity from that premise and applies the
published `RenardCartan.isOmegaCompatible_standardLevi_of_restriction`.
The supplied Levi class is compatible with the same centralizer by the
representative-independence result. The published
`omegaCompatibleApartmentUniqueness` proof then identifies the two actual
classes. Consequently every ambient apartment point restricts to a point
in the prescribed supplied class.

All fields, groups and torus schemes retain arbitrary universe `u`; the
local fields have no characteristic, rank, splitness, ramification or
residue-characteristic restriction. The comparison constructs no available
assignment. The source geometry, special-vertex preservation and exact
compact-subgroup equality remain separate obligations.

The provenance is an internal derivation from the named published Library
results and definitions. No external Lean implementation is adopted.

Author: Worker 123.
