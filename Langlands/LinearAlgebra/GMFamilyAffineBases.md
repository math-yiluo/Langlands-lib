# Basis intersections and exchange of a normal

`AffineBases` indexes the full-rank intersections of a system of affine
linear inequalities by subsets of the labelled normals. `vertex` assigns the
given intercepts on the basis, and `slack` compares the evaluation of any
normal at that functional to its intercept. A slack outside the basis is a
nonzero linear form in the intercepts, and the outside slacks of a single
basis are pairwise nonproportional. `weight` includes the product of the
parameter evaluations outside the basis.

The Gram volume is invariant under reindexing, detects independence and is
the absolute determinant in full orthonormal coordinates. With one additional
normal, `dependence` is its coordinate expansion in the basis, with coefficient
`−1` on the new label. `gramVolume_exchange` uses Cramer's rule to compute the
volume after deleting any label of the enlarged set. The slack of the deleted
inequality and the original slack are related by its dependence coefficient.
These linear algebra constructions supply the proof of affine coefficient
invariance.
