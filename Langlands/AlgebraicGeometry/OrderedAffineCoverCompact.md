# Finite ordered affine covers of quasi-compact schemes

`AlgebraicGeometry.Scheme.OrderedAffineCover.ofCompactSpace X` chooses
an actual `X.OrderedAffineCover` for every scheme `X : Scheme.{u}` with
`CompactSpace X`. The universe `u` is arbitrary.

The resulting cover has a finite, linearly ordered index type in
`Type u`, affine open subsets of `X`, and supremum equal to the top
open. These are the fields of the published `Scheme.OrderedAffineCover`
structure. The definition makes no choice of an affine cover part of
its input and applies also to the empty scheme.

This is an internal construction from Mathlib's affine-open basis and
compactness. `X.isBasis_affineOpens.exists_finite_of_isCompact`, applied
to the top open, gives a finite set `Us` of affine opens whose supremum
is top. Its subtype supplies the index type, its finiteness supplies a
`Fintype`, and transport along `Fintype.equivFin Us` supplies a linear
order. The opens are the subtype values. Classical choice selects the
resulting ordered cover from this existence proof.

No separatedness, noetherian, reducedness, projectivity, or base
assumption is used. This constructor only supplies the cover datum;
it proves no Čech acyclicity, cohomology base change, or relative cube
theorem.
