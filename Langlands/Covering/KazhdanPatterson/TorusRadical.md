# The center and maximal abelian subgroups of the diagonal cover

For the cocycle extension `TorusCover`, `torusRadical` is the kernel of the
commutator pairing viewed as a homomorphism from the diagonal group to its
character group with values in the coefficients. `torusCover_center_eq`
identifies the center as the full inverse image of this kernel.

For a skew symbol \(H\), the commutator pairing against the tuple with \(a\)
in coordinate \(i\) and one elsewhere is
\[
H\left(\left(\prod_j t_j\right)^{2c+1}/t_i,a\right).
\]
The determinant of that test tuple is \(a\), and only the \(i\)-th term of
the diagonal product contributes. The test tuples generate the diagonal
group, so `mem_torusRadical_iff_coordinate` gives a coordinate criterion
for the radical. With the hypothesis that the left radical of \(H\) consists
of the \(e\)-th powers, `torusCover_mem_center_iff_powers` expresses this as a
power condition in each coordinate.

`IsTorusIsotropic` says that the commutator pairing takes the value one on
every pair of elements of a diagonal subgroup. Injectivity of the coefficient
inclusion shows that a subgroup of the cover is abelian exactly when its
image is isotropic. Surjectivity of the projection means that the image of
a full inverse image recovers the original subgroup. Thus a maximal abelian
subgroup equals the full inverse image of its isotropic image, and maximality
passes in both directions in `torusCover_maximalAbelian_iff`.

## Source

Kazhdan and Patterson, *Metaplectic forms*, §0.1, printed pp. 39 and 41,
PDF pp. 6 and 8, give the diagonal commutator and the determinant twist.
Section 0.3, printed p. 53, PDF p. 20, defines the commutator radical and
identifies maximal abelian subgroups with inverse images of maximal
isotropic subgroups. The Lean results give the algebraic assertions for
a bilinear pairing, using skewness only for the coordinate formula.
Literature ID `kazhdan-patterson-1984-metaplectic-forms`,
SHA-256 `0f91142e8fc3814981fb77e3a3f05a7359ebd4a5e9afdf5386eb357cb4f2b57e`.
[DOI](https://doi.org/10.1007/BF02698770)
