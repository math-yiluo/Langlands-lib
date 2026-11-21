# Normalized adapted bases near a lattice norm

`VectorNorm.IsNormalizedBasis μ b` means that `b` is adapted to `μ` and that
all the basis vectors have `μ`-norm one. In this basis `μ` is the maximum
of the absolute values of the coefficients. The predicate itself does not
require `μ` to be a lattice norm or the field to be discretely valued.

For two norms adapted to a common finite basis, `ratioSup_le_ofReal_iff`
checks a nonnegative bound on their ratio supremum on the basis vectors
alone. The forward implication tests each basis vector; the reverse uses
adaptedness to bound all terms in the basis expansion. A maximal basis
ratio attains the supremum. When the basis is nonempty, the multiplicative
distance is strictly below a positive threshold exactly when all products
of a basis ratio and a reverse basis ratio are strictly below it.

Rescaling each basis vector by a unit, or reindexing, preserves adaptedness.
Rounding a norm by `VectorNorm.ballNorm` also preserves adaptedness of a
basis: the rounding operation is monotone on positive inputs, and a zero
summand is handled by nonnegativity. Over the proper nontrivially normed
field, with the finite-dimensional nonzero module of dimension `d + 1`,
let `ϖ` satisfy `IsMaxBelowOne` and put `q = ‖ϖ‖⁻¹`. If `μ` is a lattice
norm and `distRatio ν μ < q`, `eq_ballNorm` identifies `μ` with a rounded
ball norm of `ν`. A basis adapted to `ν` thus also adapts to `μ`. Each
positive lattice weight is a scalar absolute value, so invert those
scalars to normalize the basis for `μ` and then sort the `ν`-weights by a
permutation. This proves `exists_normalized_sorted_basis_of_distRatio_lt`.

These are internal consequences of the Library's single-norm adapted basis
and rounded-ball classification, for the geometry of Harris's thickened
stars. They neither establish a common basis for arbitrary pairs of norms
nor identify the sorted-weight star region with the global vertex star.
