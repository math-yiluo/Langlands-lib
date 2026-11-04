# Unipotent sources with solvable normal closure

This internal prerequisite concerns the actual smooth connected normal closure
`D` of a homomorphism `j : H → G` over an algebraically closed field.
If `G` is smooth, connected and affine, `H` is unipotent, and `D` is solvable,
then `D` is unipotent. In a pseudo-reductive ambient group the all-test image
of `j` is consequently trivial. Neither conclusion requires torusness of an
arbitrary normal solvable subgroup.

`SmoothConnectedNormalClosure.diagonalKernelEmbedding` first constructs the actual
closed embedding of the normal closure into the diagonal kernel of any supplied
compatible triangular representation. The solvable specialization then obtains
such a representation by the existing ambient Lie–Kolchin construction.

The implemented proof uses a compatible faithful ambient representation in which
`D` is upper triangular. Its diagonal target is the concrete split diagonal
torus. The original source factors through `D`, and unipotence makes its
composite with the diagonal homomorphism trivial. The proved universal
diagonal-invariance theorem then shows that the entire conjugation morphism
`G × H → G` factors through the actual diagonal kernel inside `D`.
The closed-envelope minimality of `D` gives a closed embedding of `D` into
that kernel. The kernel is unipotent by its closed embedding in the concrete
unitriangular group, without any smoothness or connectedness assertion about
the whole kernel. Closed-subgroup inheritance proves unipotence of `D`.
Pseudo-reductivity kills this smooth connected normal unipotent closure, and
its containment of the original image proves the final subgroup-functor
equality on every test scheme.

This is derived internal content assembled from the existing Library
triangularization, diagonal invariance, kernel, and image-generation proofs.
It does not prove the host positive-root uniqueness statement or construct
a homogeneous quotient curve.
