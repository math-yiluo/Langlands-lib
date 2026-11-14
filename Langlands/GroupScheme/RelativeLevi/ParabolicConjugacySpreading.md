# Spreading parabolic conjugacy from a field point

This derived internal construction applies the local equality result of
`ParabolicFieldPointEquality` to two relative parabolic subgroups containing a
common closed fibrewise maximal relative torus. It retains
`RelativeParabolicLieContainmentStatement` as an explicit premise. The ambient
base is any scheme; the field-valued point keeps its specified structural map.

`relativeParabolicLocalConjugacyOfFieldPoint` chooses an open neighbourhood of
the image of that field point on which a supplied global normalizer section
conjugates the first subgroup onto the second. Its accompanying existence
lemma proves the same conclusion without choosing an open. The supplied
section belongs to the full all-test normalizer of the torus range, and its
restriction must already conjugate the two subgroup functors at the field
point. This construction neither lifts a field point to a section nor proves
the Lie-containment premise.

The proof conjugates the first parabolic by the section. Relative parabolicity
is preserved by the resulting inner automorphism. Normalization ensures that
the conjugate still contains the torus. Compose inverse and direct conjugacies
to identify the two ranges on the supplied field fibre, use the conditional
field-point local equality construction, then compose back to obtain conjugacy
on its chosen neighbourhood.

Two helpers are included. Conjugacy by the identity at any test scheme is
exactly equality of the actual pulled-back ranges. A left correction of a
conjugating point by an element of the target subgroup preserves conjugacy:
target subgroup points normalize it, so conjugacies compose. Both helpers use
the all-test `IsConjugatingPoint` API from `LocalSubgroupConjugacy`.
