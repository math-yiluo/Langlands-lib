# Bounds for convolution against actual Levi cusp tests

`Langlands.Global.StandardParabolicFamily.HasWeightedLeviTestBound`
requires a bound for \(H_\rho(m)^r|\psi(m)|\) on a suitable
representative \(m\) of each norm-one rational Levi class. The bound
may depend on the nonnegative real exponent \(r\). The height is
computed after mapping the Levi into the ambient adelic group.

For an actual Levi cusp form with maximal infinite Levi compact,
`IsLeviCuspForm.hasWeightedLeviTestBound` applies rapid decay on the
norm-one quotient to the restricted representation. Evaluation of the
restricted representation at a Levi point has the same height as
evaluation of the ambient representation at its image. A natural power
of this height bounds the requested real power because the height is
at least one.

`HasWeightedLeviTestBound.compactPairingMajorant` uses the same Levi
representative throughout the prescribed compact set of right
translations. Submultiplicativity separates the height of the Levi
point from the bounded height of those translations. The weighted
bound therefore gives a constant majorant, integrable by finite volume
of the norm-one Levi quotient. For continuous moderate input invariant
under the rational Levi, `leviPairing_rightConvolution_of_cuspForm`
now computes the absolutely convergent pairing of the convolution as
the convolution of the scalar pairings.
`InCuspidalAnnihilator.rightConvolution_of_moderate` applies this
identity to all cusp tests at the specified infinite compact.

The argument supplies the absolute convergence for commuting
convolution with the norm-one cusp tests of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §6.2, (6.8),
pp. 201–202. The application to the uniform equations follows the
convolution step of Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series*, I.4.5, printed pp. 60–62
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`,
and `moeglin-waldspurger-1995-spectral-decomposition`, collection
fingerprint `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
