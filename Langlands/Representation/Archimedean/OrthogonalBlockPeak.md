# A polynomial weight for a block-diagonal subgroup of `O(n)`

The proposition `OrthogonalBlockPeakStatement` uses a real label \(d_i\) for
each coordinate. The associated block-diagonal subgroup consists of the
orthogonal matrices whose \(ij\) entry vanishes whenever \(d_i\ne d_j\).
The proposition supplies a continuous real function \(p\) of the matrix
entries, also polynomial when regarded as a complex-valued function. Its
values lie in \([0,1]\), its level one is exactly that subgroup, and left
multiplication by the subgroup preserves it.

The proof writes \(D=\operatorname{diag}(d_i)\) and takes the sum \(E(k)\)
of the squares of the entries of \(k^{\mathsf T}Dk-D\). This is zero exactly
when \(D\) and \(k\) commute. In entries, the commutation equations are
\((d_i-d_j)k_{ij}=0\). If \(h\) belongs to the subgroup, then
\((hk)^{\mathsf T}D(hk)=k^{\mathsf T}Dk\), so \(E(hk)=E(k)\).
The normalizing constant \(C\) is chosen above the compact upper bound of
\(E\), and the weight is \(p(k)=1-E(k)/C\).

This is an internal construction in the Library's compact polynomial
model. It provides a weight for concentrating integrals on the compact
block-diagonal subgroup in the positivity argument for induction in
stages.
