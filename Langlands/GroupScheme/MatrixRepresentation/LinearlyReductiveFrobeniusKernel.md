# The first Frobenius kernel of a linearly reductive group

`LinearlyReductiveFrobeniusKernelStatement` records the first-kernel implication
used in Frobenius induction, and `linearlyReductiveFrobeniusKernel` proves it.
For a closed finite coordinate representation of an affine linearly reductive
algebraic group over an algebraically closed field of characteristic `p > 1`,
the actual kernel of the first matrix Frobenius of that representation is of
multiplicative type. The ambient group may be disconnected or nonreduced. The affine hypothesis
and the supplied closed representation suffice for the proof.

The kernel is finite by pullback from the finite matrix Frobenius composite.
In the universal matrix of the kernel, the characteristic powers of the
entries and inverse entries are those of the identity. The closed embedding
is a quotient on coordinate algebras. Polynomial generation by the matrix
entries and inverse entries therefore puts every characteristic power in
the scalars, where augmentation determines it.

Choose the common eigenbasis of the tangent matrices of the ambient
representation. Restrict the conjugate representation to the same kernel.
It is still a closed representation and its tangent matrices are diagonal.
The height-one diagonal criterion gives multiplicative type of the kernel.
This implements the first-kernel step of Demazure and Gabriel,
*Groupes algébriques I* (1970), IV §3, Lemma 3.7, printed pp. 510–511,
using the entrywise matrix Frobenius over the unchanged ground field.
