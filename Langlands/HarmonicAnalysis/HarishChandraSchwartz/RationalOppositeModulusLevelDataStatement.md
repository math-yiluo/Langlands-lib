# Actual opposite-radical modulus levels and height comparison

`Langlands.HarishChandraSchwartz.RationalOppositeModulusLevelDataStatement.{u}`
states the comparison used to deduce weighted integrability in Waldspurger II.4.2.

Let F be a nonarchimedean local field, G an affine connected reductive group
of finite type over F, i a maximal split torus, ν generic and ζ standard for
J. Let K be any compact open subgroup with the actual minimal Iwasawa
factorization, and ρ any closed matrix representation of nonzero size.
Write U = `oppositeUnipotent i ζ`, q = `LocalField.residueCardinality F`,
w(u) = `iwasawaWeight hPK (rationalMinimalModulus i ν) u`, and
σ = `rationalHeight ρ`.

The proposition asks for a measurable integer function L on U such that
w(u) = q^(-L(u)/2), together with `LevelHeightComparison U L q σ`.
Thus there are C₀, C₁, C₂ with C₁,C₂ > 0 and

```
C₁ (1 + σ(u)) ≤ C₀ + L(u) log(q) ≤ C₂ (1 + σ(u)).
```

The group U(-ζ) is opposite to the chamber defining w.

The source is II.3.4, printed pp.256–257, together with the integer levels
used at the opening of II.4, printed p.259. The displayed comparison is its
outer comparison for the minimal parabolic, restricted to the opposite
standard radical. The actual q, arbitrary compact Iwasawa factor and
arbitrary closed representation make this a derived formulation: the source
uses its fixed special compact and embedding. The exact integer levels use
the normalization of algebraic-character norms by the residue cardinality.
Measurability of the levels and both inequalities are conclusions.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), registered as `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
PDF page = printed page minus 234.
