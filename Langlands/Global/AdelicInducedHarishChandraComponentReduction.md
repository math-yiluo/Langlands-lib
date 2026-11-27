# The uniform convolution equation from stable cuspidal representatives

`Langlands.Global.AdelicGroupPoints.compactProfileSubmodule` consists
of continuous adelic functions whose right translates restricted
to the infinite compact subgroup lie in a prescribed coefficient
space. The defining condition is linear.

`hasConvolutionEquationAt_of_cuspidalRepresentativeSpaces` assumes
that the nested norm-one cusp tests detect the moderate functions on
the inducing quotient. For each smaller standard parabolic it takes
a finite-dimensional space of moderate continuous representatives,
including a representative of the cuspidal class of the input's
constant term. These spaces must be stable under transported
convolution by the localized kernels whose outputs satisfy the
prescribed compact coefficient condition. The infinite compacts
used for the Levi cusp tests are assumed maximal.

The proof maps the representative spaces into the corresponding
cuspidal quotients. The common model is the preimage of their product
under the nested cuspidal quotient map, intersected with the compact
coefficient condition. Injectivity of the nested map makes that
model finite-dimensional. The proof uses two compact reproducing
weights. After each transported convolution with the resulting
two-sided averaged kernel, the actual nested constant-term formula
and preservation of equality of cuspidal classes give the required
representative. The left kernel average imposes the compact coefficient
condition on the output, so the operator preserves the common model.

At the base parameter the proof chooses an invertible convolution by
approximating an identity matrix on finitely many point evaluations.
The approximate kernels are supported over the prescribed open
finite adelic subgroup, and averaging over the infinite compact
preserves this support. The resulting kernel is smooth and bi-finite.
In the finite model, the usual characteristic polynomial construction
gives the entire coefficients and the pointwise convolution equation.

This is the finite-dimensional operator step of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, Lemma 8.3,
p. 223, and Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series*, I.4.5, printed pp. 60–62
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`,
and `moeglin-waldspurger-1995-spectral-decomposition`, collection
fingerprint `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
