# Full unipotent covariance of the actual scalar Jacquet integral

`Langlands.Whittaker.TwoBlockJacquetCovarianceStatement` asserts covariance of
the scalar Jacquet integral for the actual ordered canonical normalized
two-block induction. The scalar functional on the inducing tensor carrier is
the product of two actual factor Whittaker functionals. For every upper
unipotent matrix `u`, right translation by `u` preserves integrability and
multiplies the integral by the positive standard Whittaker character of `u`.
The measure may be any additive Haar measure on the exchanged rectangular
matrix space, with the canonical p-adic topology and Borel structure.

Initial integrability is an explicit hypothesis. There is no assertion that
every vector of the ambient induced representation has a convergent Jacquet
integral. Both factor carriers lie in a common universe, independently of the
field universe; the parent extension statement can place its original
carriers in a common universe by its displayed `ULift` constructions.

This is a derived internal prerequisite for the extension construction.
Decomposing a full upper unipotent matrix in the exchanged block order gives
two diagonal upper unipotent blocks followed by the exchanged rectangular
radical. Actual inducing covariance supplies the scalar left covariance for
the two diagonal blocks. The diagonal and radical scalar Jacquet identities
then give the asserted law. The product of their characters is the full
standard character, and determinant one eliminates the diagonal measure
factor. These ingredients identify the intended mathematical content; this
file states the proposition and does not supply its proof.

The assertion constructs neither a functional on all of the induction nor a
vector with a prescribed coefficient. Those remain separate steps in the
JPSS extension theorem.
