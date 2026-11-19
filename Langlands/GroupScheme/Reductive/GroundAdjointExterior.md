# Ground-field exterior representations with a maximal simple weight

Let \(G\) be an affine group scheme locally of finite type over a field \(k\),
and let the extension field \(K\) carry a split pinning of \(G_K\). For a finite
set \(O\) of simple roots, write \(\delta\) for the Library's positive-root sum
and \(s_O\) for the sum of the roots in \(O\).

`SplitPinning.groundAdjointExterior` constructs the exterior power of the
adjoint representation of \(G\) in degree equal to the number of positive
roots minus \(|O|\). Its finite coordinates are reindexed by `Fin (m + 1)`.
The positive-root indices outside \(O\) form a subset of that degree, so the
exterior coordinate type is nonempty. The adjoint representation, exterior
power and reindexing give an actual matrix representation over \(k\).

After extension to \(K\), the adjoint weight basis has one vector at each
root and weight zero on the other vectors. The exterior basis has one vector
for each subset of the prescribed size, with weight the sum over that subset.
The subset of positive roots outside \(O\) has weight \(\delta - s_O\).
The finite-subset comparison shows that every other subset has a weight
whose difference from \(\delta - s_O\) lies outside the simple-root monoid.
Since that monoid contains zero, the weight-space dimension formula gives
multiplicity one. The same formula shows that every nonzero weight space
comes from a basis index, so the comparison proves maximality.

`GaloisPinningData.exists_groundRepresentation_positiveRootSum_sub_simpleRoots`
gives the existential result for the associated split pinning. The construction
applies to \(O = \varnothing\) and to exterior degree zero. The arguments on
affine test algebras apply in all characteristics and over imperfect fields.
This is a derived construction using the Library's adjoint and exterior
representation formulas.
