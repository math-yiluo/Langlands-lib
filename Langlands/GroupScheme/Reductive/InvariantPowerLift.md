# Finite coordinate power lifting from geometric reductivity

Worker 690.

This derived interface applies the existing `IsGeometricallyReductive`
predicate to a supplied finite representation and a nonzero functional fixed
by its dual. It keeps geometric reductivity explicit and does not prove that
any particular group has this property.

`MatrixRepresentation.exists_normalized_transpose_invariant` applies geometric
reductivity to the dual representation. Evaluating invariance at the inverse
group point changes the inverse transpose into the transpose of the original
matrix. Multiplication by the inverse of the nonzero scalar value normalizes
the resulting homogeneous polynomial to take value one on the functional.
Its degree is positive, and its invariance includes every relative scheme.

For every algebra, a normalized homogeneous polynomial evaluated on the
family `c_j b` equals `b^d`. The proof is homogeneous scaling followed by
compatibility of evaluation with scalar change. Consequently, if an algebra
map sends a finite family `f_j` to `c_j b`, evaluating the polynomial in that
family lifts the power `b^d`. No surjectivity of the algebra map is required.
If each member of the family belongs to an ideal, the evaluation does too:
pass to the quotient ring, where all coordinates vanish, and apply
positive-degree homogeneous scaling by zero.

Finally, `isRightInvariant_eval₂` treats a finite family of actual global
sections on an ambient group. `IsRightCovariantFamily` specifies their
transformation under right multiplication by the subgroup on every relative
scheme. Evaluation of a transpose-invariant polynomial gives an actual
right-invariant section. Pullback of polynomial evaluation and the covariance
formula prove this directly.

The provenance is the published geometric-reductivity predicate, dual-matrix
formula, homogeneous scaling theorem, polynomial evaluation naturality and
right-invariance definition. This interface supplies finite algebra steps for
a later affine-quotient proof; it asserts neither local finiteness of an
arbitrary algebra action nor affineness of a homogeneous quotient.
