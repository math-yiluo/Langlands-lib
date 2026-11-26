# Iwasawa decomposition at the standard integral subgroup of `GL_N`

`Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralIwasawaStatement`
specializes the initial compactness assertion and part (1) of Renard V.5.1.
For a nonarchimedean local field `F`, the subgroup `K` is the integral-point
image of the standard model of `GL_N`. The parabolic is the actual
`standardParabolicPoints i ν ∅`, with `i` the diagonal torus and `ν` any
generic cocharacter of it. This is the minimal standard parabolic for
the positive system selected by `ν`.
[Integral model](../../GroupScheme/IntegralModel/GeneralLinearLattice.md)
[Minimal standard parabolic](../../GroupScheme/Rational/MinimalStandardDynamicComparison.md)

In the canonical topology on the rational points, `K` is compact and open,
and every compact subgroup containing `K` equals `K`. The products `P K`
and `K P` both cover `GL_N(F)`. The proposition uses
`IsCompactOpenMaximal` and `Iwasawa.PointProductEqualities` for these two
conclusions at the same subgroup.
[Compactness predicate](Properties.md)
[Product predicate](../Iwasawa/PointProducts.md)

This is a derived specialization of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Theorem V.5.1, opening assertion and part (1), printed p. 122 /
PDF p. 128. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
