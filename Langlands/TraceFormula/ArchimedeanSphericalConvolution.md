# Commutativity of spherical convolution at archimedean places

`ArchimedeanSphericalConvolutionStatement` compares the two convolution
integrals of functions on \(\mathrm{GL}_n(F)\) that are bi-invariant under
the standard compact subgroup. The field is real or complex in the
`RCLike` sense, and the measure is a regular left Haar measure.

The proof uses polar factorization \(g=ka\) with \(k\) unitary and \(a\)
positive definite Hermitian. Then \(g^*=k^{-1}gk^{-1}\), so taking the
adjoint preserves each compact double coset. The group automorphism
\(g\mapsto (g^*)^{-1}\) is involutive, hence preserves Haar measure.
Convolution preserves bi-invariance by left translation in its defining
integral. Applying the automorphism and then left translation in the
convolution integral reverses the factors, which is Gelfand's
commutativity argument.

This is the archimedean counterpart of the convolution argument in
`Langlands.Representation.Hecke.GelfandTrick` for compact-open subgroups.
Commuting spherical convolution provides a setting for the
archimedean separation in the trace comparison of Arthur–Clozel (1989),
Chapter 1, § 4, printed p. 44 (PDF p. 58).
