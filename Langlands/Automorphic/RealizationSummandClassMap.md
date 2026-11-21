# Classes of positive-central invariant cuspidal forms

This is the class-map part of the proof of
`GeneralLinearCuspidalRealizationSummandStatement`, the realization-to-summand direction of
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Theorem 9.7.3, p. 265.
It uses the given descent hypothesis and the Library's definitions of functions and cuspidality.

Each realized vector has a unique continuous representative on the positive-central quotient
`Q`: existence is the hypothesis, and pullback and transport to the matrix model are injective.
Those maps are linear, so the chosen representative is linear in the vector. Its pullback to
the principal quotient is the original quotient function. The band square-integrability result
`memLp_translate_of_cuspidal` at the identity and `memLp_of_comp_projection` show the
representative belongs to `L²(Q)`. The proper parabolic periods satisfy the Library's
cuspidal conditions by `mem_normalizedGeneralLinearParabolicCuspidal_iff` and
`mem_aeParabolicCuspidalFunctionSubmodule_of_continuous`. These conditions pass to the almost
everywhere class by `mem_aeParabolicCuspidalFunctionSubmodule_congr`.

The resulting linear map `classMap` into the full AE cuspidal submodule satisfies
`IsGeneralLinearFormClass` for each vector. It is injective because the quotient measure charges
nonempty open sets, so two continuous representatives with the same class agree everywhere.
Right translations commute with the projection to `Q`, yielding the finite and archimedean
compact intertwining identities from `toQuotient_finite` and `toQuotient_compact`.

Nontriviality of the source, injectivity of descent, and band square integrability give
finiteness of `bandConstant`. Thus any `L²(Q)` vector in the full cuspidal submodule can be
pulled back as a band `L²` class. Pairing that pullback with a translated original form gives
`bandConstant.toReal` times the pairing on `Q`, by `integral_band` and the almost-everywhere
representative formulas for `L²` classes and their translates.
