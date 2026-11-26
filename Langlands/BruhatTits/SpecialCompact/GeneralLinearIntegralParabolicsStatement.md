# Integral Weyl representatives and standard parabolic factorization for `GL_N`

`Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralParabolicsStatement`
specializes Renard V.5.1(2)–(3) to the standard integral subgroup of `GL_N`
over a nonarchimedean local field. It uses the integral-point image `K`
of `GeneralLinear.standardIntegralModel`, the standard diagonal torus
`i`, and every generic cocharacter `ν` of that torus.
[Integral model](../../GroupScheme/IntegralModel/GeneralLinearLattice.md)

`HasWeylRepresentatives i K` asserts that each class in the relative
Weyl group of `i` is represented by a normalizer point in `K`.
`HasParabolicFactorization i ν K` asserts the subset identity
`K ∩ P = (K ∩ M)(K ∩ U)` for each standard parabolic selected by `ν`,
with its actual standard Levi `M` and unipotent radical `U`.
[Shared predicates](Properties.md)

This is a derived specialization of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Theorem V.5.1(2)–(3), printed p. 122 / PDF p. 128. The
registered source ID is `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
