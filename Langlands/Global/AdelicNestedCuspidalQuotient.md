# Finite-dimensional spaces from nested cuspidal tests

`Langlands.Global.StandardParabolicFamily.cuspidalConstraintSpace`
is a subspace of continuous functions on \(G(\mathbb A)\). Its vectors
have moderate growth on the quotient
\(U_P(\mathbb A)M_P(F)\backslash G(\mathbb A)\). For each standard
\(Q\le P\), the class of their constant term along \(Q\), modulo the
cuspidal annihilator along \(Q\), belongs to a prescribed subspace
\(V_Q\). The annihilator uses the fibrewise pairings on the norm-one
Levi quotient, with absolute integrability as part of the zero test.

`nestedConstantTermOnModerate` uses continuity and the inducing left
invariance to prove absolute integrability on the compact radical
quotient. The normalized integral is therefore linear on the
moderate subspace. `nestedCuspidalQuotientMap` applies all these
constant terms followed by their quotient maps. The parabolic
vanishing criterion, when supplied with the required Iwasawa coverage
and closed representation, says that the kernel of this map is zero.

`finiteDimensional_cuspidalConstraintSpace` restricts this injective
map to the preimage of the product of the prescribed \(V_Q\). The
set of standard parabolics under \(P\) is finite because their indices
are subsets of the finite set of simple relative roots. Consequently
the preimage is finite-dimensional if every \(V_Q\) is finite-dimensional.

`twistedConvolutionEnd_mem_cuspidalConstraintSpace` applies the
transported convolution formula to the nested constant terms.
Preservation of moderate growth and left invariance supplies the
ambient domain condition. The remaining membership conditions are
exactly the preservation of the prescribed cuspidal classes by that
formula.

The quotient construction is derived from the norm-one pairings and
vanishing criterion in Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, (6.8), pp. 201–202, and (8.1),
pp. 221–222
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
It expresses the use of finite-dimensional cuspidal component spaces
and cuspidal detection in Mœglin–Waldspurger, *Spectral Decomposition
and Eisenstein Series*, I.4.5, printed pp. 60–62
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
