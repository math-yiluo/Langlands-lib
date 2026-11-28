# The upper triangular unit group of an idempotent

Let \(e\) be an idempotent in an algebra \(A\) over a field \(F\).
Write \(M\) for the centralizer of \(e\) and \(U=eA(1-e)\) for the
upper corner. `parabolicSubalgebra` is the subalgebra of elements
\(a\) satisfying \((1-e)ae=0\). `parabolicUnits` is the image of its
units in \(A^\times\). In finite dimension, `mem_parabolicUnits_iff_of_finite`
shows that an ambient unit belongs to this subgroup exactly when its
opposite corner is zero. The proof uses injectivity and hence
surjectivity of left multiplication on the finite-dimensional
subalgebra to construct an inverse there. With a Hausdorff ring topology
on \(A\), the zero-corner condition also proves closedness in \(A^\times\).

## Levi and upper-corner coordinates

`parabolicDiagonal` is the algebra homomorphism to \(M\) that takes
the two diagonal blocks. The zero opposite corner makes the projection
multiplicative. Products of two upper-corner elements are zero, so
`upperCornerUnit` takes \(Z\in U\) to \(1+Z\) with inverse \(1-Z\).
These units form the subgroup `upperCornerUnits`. In a topological
ring, `upperCornerUnitsEquiv` identifies that subgroup continuously with
the additive group of \(U\), using \(g\mapsto g-1\) in the inverse direction.

The units of \(M\) normalize this subgroup since left and right
multiplication by Levi elements preserve the upper corner. For a
parabolic unit \(g\), let \(m\) be its diagonal part, which is a unit
by the algebra homomorphism. If \(w\) is the upper corner of \(g\),
then \(g=m(1+m^{-1}w)\). This factorization is
`exists_levi_mul_upperCornerUnit`.

For \(Y\in M\), the identity in `upperCornerUnit_inv_conj` is
\[
  (1-Z)Y(1+Z)=Y+YZ-ZY.
\]
The quadratic term \(ZYZ\) vanishes because \(YZ\) belongs to \(U\).

## Source

For the unit group of a finite-dimensional semisimple algebra over a
characteristic-zero local field, the subgroup above gives the
parabolic attached to the idempotent. The factorization into the Levi
and \(1+U\) supplies the group coordinates used in Lemma 1.5.
The affine conjugation formula gives the change of variables underlying
Lemma 1.6 in this setting. See Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups*,
University Lecture Series 16, 1999, §1.2, pp. 7–8.
