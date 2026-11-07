# Actual ambient root data for inner unitary Jacquet exponents

Worker 17. This internal construction combines the actual nested-parabolic
geometry with the normalized Jacquet exponent comparisons for Renard VII.2.3.
It retains the original outer parabolic and Levi, the inner parabolic and
common Levi, both matching geometric radicals, and both split components.

`UnitaryInnerRootData` contains an actual fine ambient parabolic with that
same common Levi, matching radical and multiplication isomorphism. The
common-Levi equality and parabolic intersection hold on every test scheme.
It also contains compatible root presentations of the fine ambient triple
and the original outer triple. The ambient extension theorem constructs the
geometry, and normalized-exponent temperedness supplies both presentations.
`unitaryInnerRootData` chooses these data without assuming any compatible
inner presentation.

For every supplied compatible inner presentation, the real part of each
inner normalized Jacquet exponent of the outer unitary part belongs to its
nonnegative cone. Actual normalized Jacquet transitivity and injectivity
make that character an exponent of the fine ambient Jacquet module, on
the same original split component. Temperedness gives fine-cone membership.
The unitary-part restriction theorem gives zero restriction to the original
outer split component. The two constructed component factors agree by
cancellation of the original closed split-component and common-Levi maps.
The actual nested cone transfer then gives membership in the cone of the
supplied inner presentation. The affine and finite-type instances needed by
the cones follow from connected reductivity of the ambient group and the
original rational outer Levi.

This proves the exponent-membership part of the inner temperedness condition
for every supplied presentation. It does not construct an inner compatible
presentation or prove its required minimality field. That nonemptiness
condition and the complete first and third Renard targets remain obligations.
The construction and proof are derived from the imported Library results;
no further external assertion is used.
