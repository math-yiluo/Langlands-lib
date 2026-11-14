# A common normalizer for two apartment coordinates

This internal construction concerns a supplied `KPApartmentData` for a maximal
split torus of a connected reductive group over any field. All maps, sharp
fixers, and normalizers are the existing ones. It does not assume a metric,
common apartments, integer-valuedness, or a Tits-system correspondence.

The first lemma proves that the orbit under the unipotent radical of a generic
cocharacter meets the original apartment in at most one point. The quotient
relation writes an equality of apartment images as a sharp-fixer factor times
a normalizer. The published generic sharp-fixer exchange factors that fixer
into positive and negative unipotent terms and a normalizer fixing the target
point. The published opposite-unipotent normalizer separation then makes the
remaining normalizer equal to the identity. Consequently the normalizer in the
quotient relation fixes the target, and the two apartment points coincide.

The second lemma starts with a rational group element carrying two apartment
points to two apartment points. Choose a generic cocharacter nonnegative on
the displacement between the target points, using the published adapted
cocharacter lemma. The quotient relation at the first point and sharp-fixer
exchange give a positive unipotent term, a negative unipotent term, and a
normalizer matching the first pair. The positive term fixes the second target
by the depth-zero filtration inequalities. Removing it leaves a negative
unipotent element carrying an apartment point to that target. The first lemma
identifies those coordinates. The same actual normalizer therefore matches
both pairs.

`pairNormalizer` chooses such an element of the actual normalizer, and
`pairNormalizer_spec` records both endpoint equations. No uniqueness of the
chosen normalizer is asserted.

With a finite type of actual relative roots, the final theorem proves equality
of the canonical root norms of the two displacements. The original normalizer
affine map carries the source difference to the target difference, and its
linear part is the published `translationAction`. The published root-coordinate
norm is invariant under this action. Thus the comparison uses the existing
affine differences and the same root normalization on both sides.

The provenance is the existing quotient relation, generic sharp-fixer
factorization, opposite-unipotent normalizer separation, and adapted generic
cocharacter construction. The argument derives a two-point coordinate
comparison from these published algebraic inputs. It does not construct a
building metric, complete curvature structure, or coefficient action. The
root-norm consequence adds no metric or common-apartment hypothesis; it only
compares the coordinates in the displayed two endpoint equalities.
