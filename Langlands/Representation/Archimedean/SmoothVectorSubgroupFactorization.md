# Smooth-vector factorization along a linear Lie subgroup

Let \(A\) be a finite-dimensional real Banach algebra and \(R\) a jointly
continuous representation of \(A^\times\) on a complex Banach space. Let
\(G\) be a linear Lie subgroup supplied with its exponential Lie algebra
and a left Haar measure. For a genuine smooth vector \(v\) of the ambient
representation and a neighborhood \(U\) of the subgroup identity, the
statement gives finitely many genuine smooth vectors \(w_i\) and smooth
compactly supported kernels \(K_i\) on \(G\), supported in \(U\). Every
continuous scalar functional \(L\) on the ambient smooth space satisfies
\[
 L(v)=\sum_i\int_G K_i(g)\,L(R(g)w_i)\,dg .
\]
The vectors and kernels are independent of \(L\).

For a chosen finite list of directions, apply the one-parameter
factorization successively to the inverse orbit coefficient
\(x\mapsto L(R(x^{-1})v)\). Continuity of the action at a fixed point
lets the one-parameter identity apply at every base point, using the
negative of the direction to account for the inverse. Fubini and the
product of the directional kernels assemble the expression in the
reversed exponential coordinates. Choose the directions to be a basis
of the subgroup Lie algebra. On a sufficiently small coordinate ball,
the Haar density transfers the reflected kernels to smooth kernels on
\(G\). Negation preserves the real coordinate measure and converts the
inverse reversed product to the ordinary ordered product used in the
Haar chart.

This is the restriction-of-ambient-representation case of J. Dixmier
and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables* (1978), Theorem 3.3 and its use of the coordinates of
Theorem 3.1, pp. 6–9 in the retained English translation. The application
to the subgroup of right translates in a rank-raising integral uses
this form of Lemma 6.1 in H. Jacquet, *Archimedean Rankin–Selberg Integrals*
(2009), author-posted pp. 37 and 106.

`SmoothVectorMappedSubgroupFactorizationStatement` lets the subgroup
from the units of a finite-dimensional real Banach algebra `A` act on
a jointly continuous complex Banach representation of the units of a
second finite-dimensional real Banach algebra `B`. Supply a continuous
homomorphism `σ` into `Bˣ` and a real linear map `j` from the subgroup Lie
algebra to `B`. The homomorphism must take each exponential line
`exp(t • Y)` to `exp(t • j Y)`. The averages then act through `σ` on the
genuine smooth carrier for `Bˣ`, with its word-derivative topology. The
measure and the smooth compact kernels still live on the original
subgroup. A single finite family works for every continuous
complex-linear scalar evaluation, and the kernels may be supported in
any prescribed neighborhood of the subgroup identity.

The proof factors along the images of the individual exponential
lines. Group multiplication and the homomorphism preserve the inverse
orbit formula. The same Haar chart assembles these directional kernels
into subgroup kernels. Taking the two algebras equal and using the
subgroup and Lie algebra inclusions gives the restriction form above.

The registered sources are `dixmier-malliavin-1978-factorisations`,
SHA-256 `b9ae377268ddfe90468dfcf21d08ee57df6a40496ba3c57276795a8ebbf5f07f`,
and `jacquet-2009-archimedean-rankin-selberg`,
SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

`SmoothVectorCommutingDirectionsFactorizationStatement` starts with a real linear map from a finite coordinate space into the ambient Banach algebra whose images commute. It obtains a finite factorization of each genuine smooth vector by its translates along the exponentials of this map, with compact smooth kernels and Lebesgue measure in the given coordinates. The factorization holds after applying any continuous complex-linear scalar functional on the genuine smooth space, with the same vectors and kernels for every functional.

The directional proof applies in the full group of units to the negatives of the images of the coordinate directions. The exponential addition law for commuting elements identifies the inverse reversed product with the exponential of the linear combination of the original directions. This is the additive-coordinate case of the directional factorization used for row multiplication in [Jacquet, *Archimedean Rankin–Selberg Integrals*, Proposition 6.1, pp. 41–42](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=41).
