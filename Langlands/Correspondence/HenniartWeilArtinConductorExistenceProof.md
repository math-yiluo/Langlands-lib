# Integrality of the Artin conductor of a local Weil representation

`Langlands.Henniart.weilArtinConductorExistence` proves
`Langlands.Henniart.WeilArtinConductorExistenceStatement.{uK, uW}`. For each
irreducible Weil class over a p-adic field, it gives a representative and a
finite inertia presentation with surjective inertia restriction whose
rational Artin conductor is the cast of a natural number.

```lean
theorem weilArtinConductorExistence : WeilArtinConductorExistenceStatement.{uK, uW}
```

## Proof

Take a representative `A` of the class; it is continuous and irreducible. The second clause of
`Langlands.Henniart.weilConductorIntegrality` (`HenniartWeilConductorIntegralityProof`) gives,
for the continuous representation `A`, a finite inertia presentation with surjective inertia
restriction and a natural number `a` equal to its Artin expression. This presentation is a
`Ramification.Padic.FiniteInertiaPresentation`; with the representative and `a` it gives
`HasArtinConductor K σ a` by `Numerical.hasArtinConductor_iff_exists_padicPresentation`
(`HenniartPadicArtinTransport`). The class condition holds because `A` represents the class.

The integrality itself is the finite theorem: the Artin expression of a presentation is that of a
representation of the inertia group of a finite Galois extension of p-adic fields, which is a
natural number by `Ramification.Padic.exists_nat_artinConductorOfQuotient`
(`LocalFactor/Ramification/ArtinExponent`, from `finiteGaloisConductorIntegrality`). Every
presentation of every continuous representation, irreducible or not, has natural Artin and Swan
expressions (`WeilConductorIntegralityStatement`, first clause).

## Declarations

- `weilArtinConductorExistence : WeilArtinConductorExistenceStatement.{uK, uW}`.

## Source comparison

Serre's *Local Fields*, Chapter VI, §2, Theorem 1′ and its proof (printed
pp. 99–102), give nonnegative integral conductors for characters of finite
Galois groups by Brauer induction and rank-one integrality. The weighted
codimensions are in Proposition 2, Corollary 1′ (printed pp. 100–101). The
statement for the Weil group is reduced to a finite Galois extension through a
finite inertia presentation, as in Deligne, *Les constantes des équations
fonctionnelles des fonctions L*, LNM 349 (1973), §4.5 (printed pp. 537–538),
where the conductors of a Weil representation are computed on a finite
quotient of inertia.

Serre's 1979 edition is registered as `serre-1979-local-fields`.
