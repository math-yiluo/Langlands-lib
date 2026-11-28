# Compact operators with another common-Levi base cocharacter

Two base cocharacters with the same centralizer give the same Levi subgroup
on rational points. The `parameterChangeIso` between their representing
parameter schemes respects the common inclusion.
`parameterTransport_changeLevi` identifies the two characters on the Levi,
using restriction along this isomorphism on the unramified parameter
spaces. Applying `realizedTwistCoefficientEquiv` to this identity gives
the corresponding equivalence of the twisted representations.

`commonLeviCompactReindex` gives a fixed linear equivalence of the compact
pictures for any cocharacter with this centralizer, using a supplied
equivalence of untwisted representations after changing the Levi
coordinates. For an ordered pair of such cocharacters,
`commonLeviFullDomain_reindex` transports full convergence with the same
quotient Haar measure. Given Iwasawa factorizations and squared-modulus
compatibilities, `commonLeviCompactFamily_reindex` applies
`compactIntegral_reindex_square` to the two compact standard operators
with their `compactFamily_spec` identities. The resulting square uses
the fixed equivalences for the source and target compact pictures.

These coordinate identities derive from the compact realization of
normalized induction and the standard integral. See Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, I.3, printed p. 243 for normalized induction, and IV.1,
printed pp. 276–278 for compact restriction, the isomorphic-representative
diagram on p. 277, and the weak standard integral on pp. 277–278
(`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
