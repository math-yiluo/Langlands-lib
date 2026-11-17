# Natural maps and set sections of actual point products

This internal construction extends the actual section coordinates of
`PointProductSupport` to arbitrary coefficient maps of underlying sets.
Restriction only reindexes the point-fiber coordinates, so the resulting
`setMap` is a natural transformation of underlying set presheaves.

For a coefficientwise surjective module map, `zeroPreservingSection` chooses a
preimage for each nonzero coefficient and chooses zero over zero. Applying these
sections pointwise gives `setSection`, which is natural, preserves zero, and is
a right inverse to the actual morphism of product sheaves on every section.
Linearity of this section is not asserted.

`PointSupportSetMaps` shows that natural zero-preserving maps shrink actual germ
support. Thus every compact section lifts along a coefficientwise surjection,
for any topological point family, any site object, and without a separation
hypothesis or terminal-object assumption. This strengthens the earlier lifting
route through compact separating bounds, while leaving that API intact.

All constructions and proof steps are derived from the imported Library and
Mathlib interfaces, with independent point-index and coefficient universes.
