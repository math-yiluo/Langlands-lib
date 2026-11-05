# Finite local truncations of actual adelic group points

For a number field in arbitrary universe and an affine group scheme, `truncate`
keeps the local coordinates in a finite set of places and uses the identity at
the other places. The actual adelic point is obtained by the existing gluing
construction. Every regular function is integral at almost all finite places on
both the original point and the identity, which also proves the required
integrality for the truncated family.

The coordinate formula identifies truncation with this local family. The empty
truncation is the identity, and adjoining a place outside the finite set
multiplies by the insertion of that local coordinate.

The convergence proof uses the existing evaluation topology on actual adelic
points. For each regular function separately, the value at the original point
and at the identity are integral on a fixed cofinite set of finite places. All
truncations of this regular function therefore belong to one principal-filter
restricted product. Its topology is induced by the full product of completions.
Each local coordinate is eventually equal to the original coordinate as the
finite set increases, so the truncations converge in this principal restricted
product and then in the finite adeles. The infinite coordinates converge in
their product topology. The embedding given by all regular-function evaluations
then yields convergence of the actual group points.

Each truncation lies in the supremum of the local image subgroups, by induction
on the finite set and the insertion formula. Their convergence proves that this
subgroup is dense. Two continuous homomorphisms into any Hausdorff monoid which
agree on every local insertion agree on every truncation by the same induction.
Uniqueness of limits then proves equality of the homomorphisms.

This is internal infrastructure derived from actual local gluing, the evaluation
topology and the principal-filter restricted-product topology. It makes no
analytic modular-character or Haar-invariance assertion.
