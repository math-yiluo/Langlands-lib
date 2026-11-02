# The actual Picard diagonal over an arbitrary field

Author: Worker 509.

This internal specialization combines the published actual class-equalizer
theorem `RelativePicard.fieldPicardClassEqualizerImmersion` with the published
bridge from actual line bundles to arbitrary sections of the fppf Picard sheaf.
It concerns the unchanged `RelativePicard.classSheafPresheaf X.hom`, for any
proper scheme `X` over any field `k : Type u`.

`fieldPicardImmersedEqualizer` chooses a scheme `Z` over `Spec k`, an immersion
`ι : Z ⟶ T`, and its `RepresentsEqualizer` proof for any two sheaf sections on
any test scheme `T`. The representing property compares factorization through
`ι` with equality after every further scheme base change. The sections need
not have global line-bundle representatives.

`fieldPicardDiagonal_isImmersion` proves that the full presheaf diagonal is
representable by scheme immersions. Its only geometric hypothesis is
properness of `X → Spec k`; class-equalizer existence is supplied by
`TrivialLocusNoetherian`, rather than retained as an argument.

The implemented proofs apply the earlier `fieldPicardSectionEqualizer` and
`fieldPicardDiagonal_isImmersion_of_classEqualizers` constructions to this
published actual class-equalizer theorem. Those constructions use the common
fppf covering sieve of local representatives, glue the immersed equality loci,
and apply the diagonal-equalizer criterion. This module adds the specialization
that discharges their class-equalizer premise.

`fieldPicardDiagonal_isClosedImmersion_of_etale_atlas` applies the published
closed-diagonal criterion to the same actual class-equalizer theorem. It still
requires an actual etale-surjective atlas whose source is locally of finite
type over `Spec k`. The criterion transports the natural commutative group
structure through `RelativePicard.forgetSheafIso` and uses the field-group
closed-diagonal theorem.

All quantifiers retain universe `u`, arbitrary fields and proper schemes,
and arbitrary test schemes, including nonreduced and non-quasi-compact ones.
No projectivity, reducedness, connectedness, rational point, chosen section,
universal bundle, or normalization of global functions is required. This
module introduces no external literature result; its provenance is the
displayed composition of published constructions. It does not construct an
atlas or prove the full algebraic-space target.
