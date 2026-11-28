# Conjugacy of nilpotent endomorphisms from ranks of powers

`exists_intertwiningEquiv_of_nilpotent_rank_powers` considers nilpotent
endomorphisms \(f\) and \(g\) of two finite-dimensional left vector spaces
over the same division ring \(D\). If the ranks of \(f^m\) and \(g^m\) agree
for every \(m\ge 0\), there is a \(D\)-linear isomorphism \(e\) satisfying
\(ef=ge\). This is the rank-of-powers criterion underlying the nilpotent
Jordan classification. The proof uses complementary subspaces and
works over a noncommutative division ring.

Restrict \(f\) to its image \(P\). The rank of the \(m\)-th power of this
restriction equals the rank of \(f^{m+1}\) since \(f\) maps the whole space
onto \(P\). Write \(i\colon W \hookrightarrow P\) for the inclusion of a
complement of \(f(P)\) in \(P\), choose a linear section \(s\) of \(f\)
onto \(P\), and choose a complement \(Z\) of \(P\cap\ker f\) in
\(\ker f\). The proof gives coordinates
\((p,w,z)\mapsto p+s(i(w))+z\). Applying \(f\) shows that a vector with
zero image under the coordinate map must have \(w=0\), and disjointness
then forces \(p=z=0\). To decompose any vector \(x\), first use the
decomposition of \(f(x)\) in \(f(P)\oplus i(W)\). The remaining vector
lies in \(\ker f\), where \(P\cap\ker f\) and \(Z\) give its remaining
coordinates. In these coordinates the endomorphism takes
\((p,w,z)\) to \((f(p)+i(w),0,0)\).

The proof inducts on a common exponent at which \(f\) and \(g\) vanish.
The exponent drops by one on their images, which gives a linear
isomorphism between the images intertwining the restrictions. Transporting
\(i\) by that isomorphism gives the complement for \(g\) with the same
parameter space \(W\). The equality of ranks at exponent zero ensures
equal total dimensions, so the two kernel complements \(Z\) have equal
dimension. The isomorphisms on the images, on \(W\) and on the kernel
complements then intertwine the two coordinate formulas.
