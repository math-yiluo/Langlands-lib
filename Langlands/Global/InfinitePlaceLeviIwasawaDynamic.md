# Archimedean Levi-compatible Iwasawa from dynamic structure

This internal assembly discharges the ambient-realization premise of
`InfinitePlaceLeviIwasawaAssembly` with the published theorem
`SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement`.
It retains two explicit universal structural premises at arbitrary
universe `u`: `ParabolicDynamicStatement` and
`DynamicGeometricUnipotentRadicalStatement`. Neither of these is proved
here.

`completion_realization_of_dynamic` applies the previous assembly with
that realization theorem. Its cocharacter is chosen over the original
number field using the two retained dynamic propositions. The
base-change identities for the dynamic parabolic and centralizer
transport the represented original inclusions to the actual completion
pullback. Connected reductivity is preserved by that field extension.
The published ambient realization theorem and the arbitrary-`RCLike`
internal conjugation construction give compatible diagonal data there.
The completion's analytic structure retains its original norm and
topology.

`exists_leviCompatibleIwasawaCompact_of_dynamic` passes these data to the
published actual-completion transport. The result is the unchanged
`IsLeviCompatibleIwasawaCompact` predicate on the original
`InfinitePlaceGroupPoints F G v`: ambient maximal compactness, ordered
parabolic-image-times-compact coverage, the intersection equality using
the actual composite `l ≫ p`, and maximal compactness of the inverse
image on the original Levi point carrier with its own evaluation
topology.

`leviCompatibleIwasawaStatement_of_dynamic` introduces every original
argument of the published `LeviCompatibleIwasawaStatement` and applies
this existence theorem. It preserves the arbitrary number field,
connected reductive group, specified rational parabolic and Levi,
infinite place, non-split and anisotropic cases, and improper
parabolics. The two dynamic propositions remain premises of the
wrapper, so this result is not by itself an unconditional proof of
`LeviCompatibleIwasawaStatement`; `InfinitePlaceLeviIwasawaProof` supplies
the two premises (`parabolicDynamic`, `dynamicGeometricUnipotentRadical`)
and proves it as `leviCompatibleIwasawaStatement`.

The provenance is internal composition of published results. In
particular, the ambient-realization proposition is now supplied by its
actual proof, rather than assumed as an additional structural premise.
The separate `ReductiveLeviIwasawa` module provides the corresponding
actual-point construction for every supplied common dynamic pair over
an `RCLike` field.
