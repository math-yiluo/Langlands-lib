# Inversion for the real triangular integral

These lemmas are internal measure and matrix helpers for the real
triangular expansion of Jacquet (2009), §4.7, pp. 30–31. They justify
changes of variables on the side containing the coefficient at
\(\iota(g)=g^{-T}\); they do not assert the integral equation.

* `realUpperEntryProductMeasure_measurePreserving_inv`: on real upper
  unitriangular matrices, inversion preserves the pushforward of the
  product of the supplied sigma-finite additive Haar measure over the
  strict upper entries. The proof expresses right translation by a fixed
  matrix as a triangular addition in those entries. A correction at
  \((i,j)\) only uses coordinates with strictly smaller index gap than
  \(j-i\). The finite triangular translation lemma gives right invariance.
  Together with the left Haar construction, this yields inversion invariance.
* `realDiagonalHaar_measurePreserving_inv`: inversion preserves the
  product measure \(\prod_i dx_i/|x_i|\) on the full diagonal units. Here
  right invariance follows from commutativity and the left Haar property.
* `realHaar_measurePreserving_inverseTranspose`: inverse transpose
  preserves any left Haar measure on the real general linear group. It
  is an involutive continuous group automorphism, and the positive Haar
  scaling character therefore equals one.
* `realInverseTranspose_unitary_eq` and `realInverseTranspose_triangularPoint`:
  inverse transpose fixes the actual real orthogonal subgroup pointwise.
  Applied to \(\operatorname{diag}(d^{-1})u^{-1}k\), its matrix is
  \((u\operatorname{diag}(d))^T k\). This is the column-scaled lower
  triangular test argument in the dual integral.
