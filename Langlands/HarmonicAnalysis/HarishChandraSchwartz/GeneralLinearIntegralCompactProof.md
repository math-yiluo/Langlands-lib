# Integral compact and Iwasawa decompositions on actual GL points

`generalLinearIntegralCompact` proves
[`GeneralLinearIntegralCompactStatement`](GeneralLinearIntegralCompactStatement.md)
for every nonarchimedean local field \(F\) and every natural rank \(N\).
Write \(K\) for the image of the standard integral model's points in the
actual rational-point group. The equivalence `rationalPointsEquiv` and
`mem_standardIntegralModel_integralPoints_iff` identify this image with
the integral matrix subgroup.

The generic and residue-field fibres of the standard model are
connected reductive by `GeneralLinear.isConnectedReductiveStatement` and
the standard base-change isomorphism. `IntegralModel.maximalCompactStatement`
and `isOpen_integralPoints_localField` give compactness, openness and
maximality among compact subgroups in the rational-point topology.
`isBoundedOpenMaximal_of_isCompactOpenMaximal` gives maximality among
algebraically bounded subgroups by taking their compact closures.

Each element of the relative Weyl quotient has a normalizer lift.
Its action on characters is a coordinate permutation. The point of
the corresponding permutation matrix has the same action on the
relative root span, so faithfulness gives the desired quotient class.
The same permutation matrix is defined over \(\mathcal O_F\), which
puts its point in \(K\) under the integral-point comparison.

The empty set of simple roots gives the singleton block shape.
Its parabolic is upper triangular under `rationalPointsEquiv`.
`Iwasawa.exists_mul_upperTriangular` makes a given matrix \(g\)
upper triangular by right multiplication by an integral \(k\).
The factors \(gk\) and \(k^{-1}\), transported to actual points,
give the ambient `IsIwasawaPair` for \(P_{\varnothing}(F)\) and \(K\).

For any standard parabolic, `generalLinearStandardParabolic`
identifies its point groups with the block matrix parabolic, Levi
and radical. The diagonal-block projection of an integral parabolic
matrix is integral by `BlockShape.leviEmbedding_leviProjection_mem`
in positive rank and trivial in rank zero. Removing this factor
on the left gives an integral element in the kernel of the Levi
projection, namely the radical. The product of the two integral
factors lies in the original compact intersection by subgroup closure.
The resulting identity is
\[
K\cap P_J(F)=(K\cap M_J(F))(K\cap U_J(F)).
\]
`standardLeviIwasawaFactorsAt_of_factorization` projects the ambient
Iwasawa decomposition from \(P_J(F)\) onto \(M_J(F)\). It uses the
identity to identify the image of \(K\cap P_J(F)\) with \(K\cap M_J(F)\),
giving the Iwasawa pair of \(P_{\varnothing}(F)\cap M_J(F)\) and
\(K\cap M_J(F)\) inside \(M_J(F)\).

## Sources

- Renard, *Représentations des groupes réductifs p-adiques*, French edition of
  9 July 2026, V.5.1(1)–(3) and the Iwasawa part of (5), printed p. 122
  (PDF p. 128). Literature ID `renard-2026-representations-groupes-reductifs-padiques`,
  SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
  Harish-Chandra)*, I.1, printed p. 240 (PDF p. 6). Literature ID
  `waldspurger-2003-plancherel`, SHA-256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
