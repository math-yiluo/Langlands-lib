# A positive spherical majorant for complex standard modules

Taking the absolute value of a complex inducing character replaces its
weight by zero and its exponent by its real part. The normalized Borel
character for these modified data is the absolute value of the original
normalized Borel character. `modulusSpherical` is a spherical vector for the
modified data with value one on the unitary group. Iwasawa decomposition
expresses its value at each group element as the absolute value of the
original Borel character on the diagonal factor. Hence its value is positive,
and any smooth vector in the original standard module is bounded pointwise by
this spherical vector times its uniform bound on the compact group.

For a strict adjacent swap, the exponents remain strictly ordered after taking
real parts. Applying `exists_strictSwapIntertwining_apply` to the positive
spherical majorant gives a vector constant on the unitary group, since the
integrand is right unitary invariant. Iwasawa decomposition shows that this
vector is the target majorant times the source chart integral at the identity.
That integral is absolutely convergent, and its real part is strictly positive
by continuity and pointwise positivity. This proves
`integral_modulusSpherical_strictSwap`, the real integral identity used to
bound repeated chart integrations.

The argument is an internal majorant construction for iterated rank-one
intertwining integrals in the strict convergence chamber. It uses the
absolute-value estimate from Iwasawa decomposition as in Wallach, *Real
Reductive Groups I* (1988), Lemma 5.3.1, printed pp. 144–145 (PDF pp. 164–165
of `wallach-1988-real-reductive-groups-i`). The iterated application is part of
the archimedean constituent step in Getz and Hahn, *An Introduction to
Automorphic Representations* (2024), Theorem 10.6.4, printed p. 286
(PDF p. 298 of `getz-hahn-2024-automorphic-representations`).
