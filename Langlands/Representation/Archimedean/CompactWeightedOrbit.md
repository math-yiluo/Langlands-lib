# Compactly parametrized bounded orbit averages

For a jointly continuous action \(R\) on a complex Banach space,
`compactWeightedOrbit` is the bounded complex linear operator
\[
v\longmapsto \int_X w(x)R(j(x))v\,d\nu(x).
\]
The parameter space is compact with a finite Borel measure, and the group
parameter \(j\) and scalar weight \(w\) are continuous. Pointwise
boundedness on the compact source gives a uniform operator bound by
Banach–Steinhaus, and the weight is bounded in the supremum norm.

For a compact subgroup \(K\) of a topological group, take \(j\) to be the
inclusion and \(\nu\) to be left invariant. A linear family of continuous
weights \(F(u)\) is indexed by a finite-dimensional matrix representation
\(\tau\) of \(K\), with \(F(\tau(k)u)(x)=F(u)(k^{-1}x)\).
Left invariance of \(\nu\) then makes \(u\mapsto\int_K F(u)(x)R(x)v\,d\nu(x)\)
a compact intertwiner for each fixed \(v\). Each value is compact-finite
in the normed action because the intertwiner's image is finite-dimensional.
If \(R\) is admissible for \(K\) and \(\tau\) is continuous, the range of the
averaging operator with any one of these weights lies in the image of
evaluation on the finite-dimensional space of compact intertwiners, so the
entire range is finite-dimensional.

This is an internal construction of the finite compact averages used in
smooth test trace separation.
