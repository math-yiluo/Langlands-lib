# The discriminant in a completed Hermitian matrix chart

Let \(K/E\) be a CM extension and \(A/K\) a degree-\(2m\) central simple
algebra with unitary involution. Supply an `EvenDiscriminantPresentation`,
a characteristic-zero extension \(F/E\) in the universe of \(E\), and a
quadratic coefficient field \(C/F\) with compatible embeddings of \(E\)
and \(K\). The nontrivial automorphism of \(C/F\) extends CM conjugation.
An \(F\)-algebra chart of \(F\otimes_E A\) in matrices over \(C\) acts on
the embedded global center through the supplied scalar map. On pure
tensors \(1\otimes a\) it takes the global involution to the adjoint for
an invertible Hermitian Gram matrix \(H\).
`discriminantClass_eq_zero_of_hermitian_chart` identifies vanishing of the
algebraic discriminant after extension to \(F\) with membership of
\(d\in F^\times\) in the norm subgroup for \(C/F\), where \(d\) maps to
\((-1)^m\det H\) in \(C\). The fields \(E\), \(K\), and \(C\) can have
independent universes.

The quadratic coefficient field has a presentation in the universe
of the base, because it is finite-dimensional. Transport the chart
and Gram matrix entrywise to this presentation. The center-compatible
chart identifies the scalar extension of the presented central simple
algebra with matrices over the presented field. The two induced
involutions agree on \(1\otimes A\), and the two center actions agree
on the original center. The Hermitian scalar-extension criterion
therefore identifies vanishing with the norm condition. Compatibility
of actual field norms under the coefficient equivalence gives the
condition on the original signed determinant.
