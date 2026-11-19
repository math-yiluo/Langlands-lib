# Ampleness of the actual finite parabolic Lie determinant dual

Authors: Worker 593 and Worker 796.

`Langlands.GroupScheme.finiteAffineParabolicDeterminantDualAmple` proves exactly
`Langlands.GroupScheme.FiniteAffineParabolicDeterminantDualAmpleStatement.{u}`
for every universe `u`. The published statement and its imported Lean/Markdown
pairs are unchanged.

For every commutative base ring, reductive group scheme, finite index type and
family of actual relative parabolic inclusions, the theorem proves ampleness
of the actual module-dual line bundle of the Lie determinant of
`parabolicRepresentative (finiteAffineParabolicFamily hG j hj)`. Its base is
the prescribed finite coproduct of the actual homogeneous quotient schemes;
its parabolic family is the actual glued universal conjugate family. There
are no additional noetherian, splitting, constant-rank, nonempty-index,
distinctness, completeness or uniform-field-type assumptions.

The implemented proof applies
`finiteAffineParabolicDeterminantDualAmple_of_jetKernels`. For each prescribed
component it uses `affineParabolicQuotientJetDataAtLeast hG i hi 1`, ensuring
positive order, and discharges the complete actual jet kernel hypothesis with
`hasStabilizedJetKernelComparison`. Affineness of the ambient group follows
from reductivity over the affine base.

The latter comparison identifies, on every affine quotient open, the actual
stabilized jet tensor kernel with the submodule classified by the retained
closed Grassmannian embedding. It pulls back along the actual smooth,
surjective affine quotient projection, uses the embedding factorization and
actual conjugate parabolic jets to compare the two kernels, and descends the
equality through the faithfully flat map on affine coefficients. The
stabilization is the genuine jet module biproduct with the pulled-back finite
projective complement.

The positivity implication then uses the actual ambient global jet generators
to realize this stabilized sheaf by the classified quotient, obtains ample
determinant from the Grassmannian, and transfers positivity from the
positive-order jet determinant to the actual Lie determinant dual. Finally
the existing finite-component determinant comparison and finite-coproduct
ampleness theorem assemble precisely the line bundle in the target. That
component assembly also covers the empty finite index type.

This is an internal proof from the existing quotient, jet, determinant and
ampleness interfaces. Its implementation is described above rather than
claimed to reproduce the literature's proof. The statement's original
geometric provenance remains the one recorded in its published Markdown.
