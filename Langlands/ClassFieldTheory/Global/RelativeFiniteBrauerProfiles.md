# Finite profiles in relative field-unit cohomology

Fix a Galois extension of number fields and an invariant family with the
relative class formation and arithmetic normalization laws. At the
chosen places above the finite places of the base, take a finitely
supported family of invariant values in the respective local
denominator subgroups. If the sum of these values is zero, there is a
relative field-unit cohomology class with exactly those local
invariants, and all of its archimedean invariants vanish
(`exists_relativeCohomology_of_finiteInvariants_archimedean`). The
statement `RelativeFiniteBrauerProfileStatement`, without the
archimedean part, is `exists_relativeCohomology_of_finiteInvariants`.

Each value has a section into the actual idele cohomology, with zero
invariants at the other finite places and with total invariant equal to
that value. The finite sum of the sections therefore has total
invariant zero. Injectivity of the assembled idele-class invariant and
its compatibility with the total invariant imply that the sum maps to
zero in idele-class cohomology
(`ideleQuotientCohomologyMap_eq_zero_of_total_eq_zero`: an element of
`H²(Gal(L/F), J_L)` of total invariant zero maps to zero in
`H²(Gal(L/F), C_L)`). Exactness lifts it to field-unit cohomology. The
local invariants of the principal class then identify the requested
values at the supported places and give zero elsewhere. The archimedean
invariant of the class is the archimedean idèle invariant of the sum
(`archimedeanIdeleInvariant_principalIdeleCohomologyMap`), which
vanishes on local sections at finite places
(`archimedeanIdeleInvariant_ideleLocalSection`).

Declarations, in order: `ideleQuotientCohomologyMap_eq_zero_of_total_eq_zero`,
`RelativeFiniteBrauerProfileStatement`,
`exists_relativeCohomology_of_finiteInvariants_archimedean`,
`exists_relativeCohomology_of_finiteInvariants`.

This is an internal consequence of the Library's local sections, global
invariant assembly, and exact cohomology sequence. The output concerns
relative cohomology for the given Galois extension. It is the
cohomological lifting step for finite Brauer profile realization.
