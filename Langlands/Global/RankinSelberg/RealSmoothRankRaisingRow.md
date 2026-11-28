# The real smooth rank-raising identity with bottom-row tests

`realSmoothRankRaisingRow` compares adjacent quotient ranks for a jointly
continuous representation of the larger real general linear group on a
complex Banach space. The scalar form on the genuine smooth vectors is
continuous and complex-linear for the word-derivative topology and
invariant under the larger upper-unipotent subgroup. At spectral points
of absolute integrability of the larger
integrands, the smaller integral at power `s - 1` becomes a finite sum of
larger integrals at power `s`, with the positive comparison scalar for the
supplied compatible measures. Each larger integral has a compactly
supported smooth test of the full bottom row, supported where its last
entry is nonzero.

Apply smooth factorization using the compensating lower subgroup. After
leading padding, the translated argument has the prescribed bottom row.
Both the row and the scalar coefficient descend under the upper
unipotent group. The factorization measure is the rectangle and trailing
product with the absolute determinant density on the trailing coordinate.
The quotient integral identity with this density identifies each averaged
term with its larger-quotient integral. Summing the terms gives the claimed
identity and the absolute integrability of the smaller integrand.

This is the one-step scalar comparison with a bottom-row test in Lemma
14.1, pp. 105–107 of the author-posted edition of
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=105).
The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

`RealMappedSmoothRankRaisingRowStatement` uses the larger real group via
a continuous homomorphism into the units of a finite-dimensional real
Banach algebra. A supplied real linear map of Lie directions intertwines
the exponentials. The representation of the target units group is jointly
continuous on a complex Banach space. The continuous complex-linear
form is on its genuine word-derivative smooth carrier and is invariant
under the image of the larger upper unipotent subgroup. The same
adjacent quotient measures, determinant shift, and compact row support
apply, with the same integrability premise for the finite larger family.

Use `realRankRaisingMappedSmoothFactorization` for the smooth averages and
apply the form after the translated padded argument through the
homomorphism. The equality on quotient representatives follows from
invariance under the upper-unipotent image. The scalar Haar comparison
then has the same integrands in the row coordinates. This accommodates
the two leading-block embeddings into the product action on p. 106 of
Jacquet. The identity homomorphism gives the single-group form above.
