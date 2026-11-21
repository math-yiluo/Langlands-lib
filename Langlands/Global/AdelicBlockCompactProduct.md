# The actual finite and infinite factors of the adelic compact model

`standardCompactProductEquiv` identifies the standard compact subgroup of the adelic general linear group with the product of its infinite compact subgroup and its finite integral subgroup. The coordinate projections preserve the subgroup conditions by `mem_standardCompact_iff`. Pairing the coordinates is the inverse. The maps inherit multiplicativity and continuity from the ambient adelic splitting.

`compactIntersectionProductEquiv` gives the corresponding multiplicative homeomorphism for the intersection of a block parabolic with the standard compact subgroup. Here each coordinate must lie in both its own parabolic and its own compact subgroup. Pairing the parabolic elements preserves both requirements. Including the intersection into the standard compact subgroup agrees with including each factor after splitting.

These are internal comparisons of actual subgroups used in the scalar compact picture. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the adelic parabolic and compact factors used to form induced sections.
