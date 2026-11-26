# The uniform equations on a standard parabolic family

`Langlands.Global.StandardInducedHarishChandraEquationsStatement` is the
positive matrix size case of the uniform convolution equations on a
standard parabolic family. It allows a complex-linear map from a
finite complex coordinate space into the character parameter space.
The compact is any maximal compact giving Iwasawa coverage for the
parabolic being twisted.

`inducedHarishChandraEquations_of_standard` reduces the original
proposition to this formulation. The rank-zero case uses a normalized
kernel on the subsingleton adelic group. In positive rank, construct
the standard family from the maximal split torus and generic
cocharacter in the supplied root presentation. At the supplied index
the represented parabolic and Levi images coincide. The description
of the geometric radical by the dynamic unipotent subgroup identifies
the two represented radical images as well.

These comparisons give the same inducing invariance subgroup and
Iwasawa coverage for the original compact. The factorization of the
standard parabolic inclusion through the supplied parabolic pulls
the parameter back by a complex-linear map. The restriction identity
for the Iwasawa heights gives equality of the two families of
functions at these parameters. An equation for the standard family
therefore has exactly the required kernels and entire coefficients
for the original twists.

This reduction implements the passage to standard parabolics for the
uniform equation of Bernstein–Lapid, *On the meromorphic continuation
of Eisenstein series*, §8.3, Lemma 8.3, p. 223. The height comparison
uses the parameter restriction in §6.10, p. 208
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
