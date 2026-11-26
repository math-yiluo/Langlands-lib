# Standard integral compact and Iwasawa decompositions for GL

`GeneralLinearIntegralCompactStatement` specializes Renard V.5.1(1)–(3)
and the Iwasawa part of (5) to the standard integral-point subgroup
\(K=\mathrm{GL}_N(\mathcal O_F)\) in the actual rational-point group, at the
diagonal torus and a reference cocharacter with strictly decreasing
integer coordinates. The local field can have either characteristic,
and the matrix rank is any natural number.

`SpecialCompactProperties` includes compactness, openness and
maximality for the rational-point topology. It also includes the
algebraically bounded version of maximality, representatives in \(K\) for
the actual relative Weyl quotient, and
\(K\cap P_J(F)=(K\cap M_J(F))(K\cap U_J(F))\) for the actual standard
subgroups. Algebraic boundedness uses the values of regular functions
on actual rational points.

`IsIwasawaPair` expresses \(G(F)=P_0(F)K\). The Iwasawa condition
inside each literal standard Levi is `StandardLeviIwasawaFactorsAt`,
using the intersections of \(P_0(F)\) and \(K\) with that Levi.
These are the compact comparisons used by the ambient and Levi
spherical functions. A geometric identification with a specified
building stabilizer is a separate comparison.

## Sources

- Renard, *Représentations des groupes réductifs p-adiques*, French edition of
  9 July 2026, V.5.1(1)–(3) and the Iwasawa part of (5), printed p. 122
  (PDF p. 128). Literature ID `renard-2026-representations-groupes-reductifs-padiques`,
  SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
  Harish-Chandra)*, I.1, printed p. 240 (PDF p. 6). Literature ID
  `waldspurger-2003-plancherel`, SHA-256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
