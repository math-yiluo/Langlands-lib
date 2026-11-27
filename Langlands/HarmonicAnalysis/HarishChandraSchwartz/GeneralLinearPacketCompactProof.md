# The common standard compact for general linear wave packets

`generalLinearPacketCompact` proves `GeneralLinearPacketCompactStatement`
for every nonarchimedean local field and natural matrix rank. A strictly
decreasing diagonal cocharacter has distinct coordinates, so it is generic.
The open subgroup in the proof is defined with underlying subgroup
\(\mathrm{GL}_N(\mathcal O_F)\), the integral points of the standard model.
`generalLinearSourceCompactGeometry` supplies the diagonal apartment, its
axioms and bounded open stabilizers, and a special vertex with norm-one
stabilizer equal to those integral points. This equality transports the
special compact properties from `generalLinearIntegralCompact` to the
vertex stabilizer.

The minimal standard parabolic has Iwasawa factorization with this compact
by `generalLinearIntegralCompact`. Every algebraic parabolic contains a
minimal parabolic. Rational conjugacy and the minimal Iwasawa factorization
allow the conjugating element to be chosen in the compact. The conjugate
minimal parabolic thus has Iwasawa factorization with the same compact, and
inclusion extends this factorization to the containing parabolic. Taking
inverses gives the other product order. The dynamic clause uses the affine
representation of the dynamic parabolic, and the standard clause uses
inclusion of the minimal standard parabolic. The conjugate clauses use
conjugation of the algebraic inclusion, the cocharacter, and the standard
parabolic rational points, respectively.

`generalLinearSimultaneousBasis` supplies the simultaneous normal
compact-open basis. `generalLinearCartanCovering` supplies the ambient
covering and the coverings in the standard Levis, where the compact is
intersected with the Levi. These results use the same integral-point
subgroup as the geometry and the parabolic products.

Waldspurger I.1 fixes one special compact for Iwasawa factorization and the
Cartan covering in (4). Renard V.5.1 gives the compact and Levi properties,
and V.5.2 gives the simultaneous basis. The geometric comparison realizes
the standard lattice stabilizer at the special vertex, as in Kaletha and
Prasad, Proposition 15.1.31.
See the [statement and its source locators](GeneralLinearPacketCompactStatement.md).
