# Partition of a truncated negative cone

The chamber argument in Delorme, *On the spectral theorem of Langlands*
(2023), §7, equation (7.26), uses an orthogonal decomposition relative to the
simple coroots. The basis formulation here applies to any finite basis with
nonpositive off-diagonal pairings for a symmetric positive definite form.
For selected indices `I`, work in the common orthogonal space of the basis
vectors in `I`. Coordinates outside `I` are the quotient coroot coordinates.
The region `basisNegativeCut` bounds these coordinates from above by those
of a dominant increment `s`.

`truncatedBasisConePartition` applies complementary polar decomposition to
write a point as `y − z` with `y` in the closed dual chamber, `z` in the
nonnegative basis cone and complementary pairings. Both terms are orthogonal
to `I`. If the pairing of `y` with an index of `I` were positive, the
corresponding coordinate of `z` would vanish. Obtuseness would make the
pairing of `z` there nonpositive, contradicting orthogonality of `y − z`.
The face index set `Q` adds to `I` precisely the indices where `z` has a
positive coordinate. The pairings of `y` vanish on `Q`. Outside `Q`, the
upper cutoff on `y − z` is the same as the cutoff on `y`.

Conversely, the closed upper cutoff on `y` makes the coordinates of `s − y`
outside `Q` nonnegative. Pairings of `s − y` on `Q` are nonnegative by
dominance of `s` and orthogonality of `y`. The obtuse-basis sign criterion
then makes every coordinate of `s − y` nonnegative. The same criterion puts
`z` in the nonnegative basis cone, using its orthogonality on `I` and the
specified coordinates outside `I`. Thus `y − z` belongs to the negative
cone translated by `s` in the quotient coordinates. Complementary polar
uniqueness fixes both terms, and the strictly positive coordinates of `z`
recover `Q` outside `I`.

The theorem uses closed inequalities on the split part and positive
coordinates on the relative interior of the selected negative face. It is
stated after translation by the base truncation parameter.
