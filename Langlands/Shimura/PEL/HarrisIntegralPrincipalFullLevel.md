# Ordered markings at principal Harris levels

Fix a polarized Harris action on a connected, locally noetherian,
quasi-separated base `S` in universe zero and a chosen algebraically closed
field-valued point of `S`. The comparison uses the existing full adelic
tower inputs. Every positive integer is invertible in the global sections
of `S`. The inputs also give finite fibres for the finite étale covers,
the torsion and roots-of-unity finite étaleness, the finite Weil transition
comparison, and the rational adelic comparison.

When the supplied compact open level has subgroup exactly the principal
congruence subgroup of positive modulus `m`, `harrisPrincipalFullLevelEquiv`
identifies normalized invariant orbits with compatible ordered full-level
markings. Both sides use the same abelian scheme, polarization and auxiliary
positive left action. The left side is the existing invariant orbit in
`PolarizedWeilLevel.levelTower` with its `HarrisIntegralLevelCondition`.
The right side is an ordinary `FullLevel` of genus \([E:\mathbf Q] n^2\)
satisfying `HarrisPrincipalFullLevelCondition`.

`harrisPrincipalSourceCoordinates` is the reindexing used in
`harrisIntegralOrderedFullLevel`. The equality `harrisIntegralSource_rank`
identifies the rank of the source lattice with twice the genus. After this
reindexing the inverse of the published residue coordinate equivalence sends
the standard coordinate module to the quotient of the actual integral
adelic source span by its `m`-multiples. The compatibility condition asks
for a normalized Weil frame at the given algebraically closed point whose
reduction in these coordinates is the fibre coordinate map of the marking.

The forward map is `harrisIntegralOrderedFullLevel`. Its fibre formula is
proved on the standard basis by the restriction and representative-independence
formulas for `harrisIntegralLevelSections` and `harrisIntegralLevelReduction`.
Linearity over `ZMod m` gives the formula on the whole module. Equal markings
give equal frame reductions, which determine the original principal right
orbit by `harrisIntegralFrameReduction_eq_iff_rightOrbit`.

For the inverse, each coordinate value of the marking is the restriction
of the corresponding linear combination of its global torsion sections.
It is fixed by monodromy by `harrisIntegralGlobalTorsionEquiv`. The compatible
frame thus has pointwise fixed reduction. The principal-level fixedness
criterion `harrisIntegralFrameReduction_fixed_iff` makes its original
right orbit monodromy invariant. Evaluations at the given point agree on
each ordered section, and restriction is injective on global torsion, so
the resulting orbit recovers the entire marking.

The internal comparison uses the same right-orbit construction as the
characteristic-zero level definition in Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties*, III.1, printed p. 91
(PDF p. 99). That definition uses all finite adeles and the actual
fundamental group of the connected test. Here the subgroup is specifically
the kernel of reduction on the integral source span, and the compatibility
test includes the existence of a Weil-similitude frame at the reference
point. The equivalence concerns levels on a supplied polarized action.

Source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
III.1, printed p. 91 (PDF p. 99).
