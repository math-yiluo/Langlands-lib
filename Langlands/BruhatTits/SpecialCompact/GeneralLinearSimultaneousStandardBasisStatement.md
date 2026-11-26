# Renard's simultaneous compact-open basis for the integral points of `GL_N`

`Langlands.BruhatTits.SpecialCompact.GeneralLinearSimultaneousStandardBasisStatement`
specializes Renard V.5.2 to the standard integral subgroup of `GL_N`. It
quantifies over nonarchimedean local fields in universe `u`, each matrix
size `N`, and every generic cocharacter `ν` of the standard diagonal
torus. The cocharacter fixes the positive system. The subgroup is the
image of the integral points of `GeneralLinear.standardIntegralModel`,
whose generic fibre is the actual `GL_N` over the field.
`GeneralLinear.mem_standardIntegralModel_integralPoints_iff` identifies these
points with the images of invertible matrices over the valuation ring.
[Integral model](../../GroupScheme/IntegralModel/GeneralLinearLattice.md)
[Matrix comparison](../../GroupScheme/IntegralModel/GeneralLinearStandardPoints.md)

The conclusion applies the published `SimultaneousStandardBasisAt` to
these data. A single basis of compact open subgroups normal in the
standard integral subgroup works for all standard parabolics at once.
For each parabolic the predicate uses an actual compatible split
component and includes Iwahori factorization, Levi normalization,
chamber contraction, exhaustion of both radicals and uniform
cofinality. It uses the canonical rational-point topology and includes
the inherited basis on each standard Levi. [Simultaneous basis
predicate](StandardBasisProperty.md)

The statement is a derived specialization of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Theorem V.5.2(i)–(iv), printed p. 123 / PDF p. 129. The
preceding V.5.1 fixes the adapted maximal compact subgroup in the book.
The specialization uses the standard integral model to give the subgroup
in the basis predicate. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
