# Surjectivity of real Borel averaging

A smooth bump on Gram matrices, centered at the identity and supported in a
compact invertible ball, gives a smooth nonnegative cutoff on the real general
linear group. Pulling the bump back under \(g\mapsto gg^{\mathsf T}\) makes it
right orthogonal invariant. A bound on the Gram trace bounds every matrix entry,
and invertibility of the Gram matrix implies invertibility of the matrix. Thus
the cutoff has compact support in the group. It equals one at the identity, so
its integral over the upper triangular group is positive.

Multiply a smooth inducing section by this cutoff and extend by zero to a smooth
matrix test. At any orthogonal matrix the inverse inducing weight in the average
cancels the left transformation of the section. Right invariance of the cutoff
then makes the average the original section times the same positive integral at
every orthogonal point. The Iwasawa decomposition and the shared left
transformation law extend the equality to the whole group. Dividing the test by
that positive integral gives a preimage of the section.

`RealBorelAverageSurjectivityStatement` records this surjectivity. The module
also proves that equality of the distributions attached to two bounded
inducing functionals implies equality of the functionals. A complex matrix test
is the sum of its real part and \(i\) times its imaginary part, so equality on
real tests suffices. This is an internal input to smooth Whittaker uniqueness.
