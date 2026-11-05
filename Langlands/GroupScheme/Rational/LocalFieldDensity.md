# Rational-point density for smooth connected affine groups over local fields

Authors: Worker 1554 and Worker 1296.

This derived internal module proves that every smooth connected affine group
scheme over an actual nonarchimedean local field has Zariski dense rational
points. The fields lie in an arbitrary universe `u`. There is no restriction
on characteristic and no reductivity premise. The rational points are actual
sections over `Spec F`, and density is the published `HasDenseRationalPoints`
predicate: the union of their images is dense in the underlying scheme.

`SmoothConnectedAffineLocalFieldDensityStatement` states that assertion.
`hasDenseRationalPoints_of_localField` proves it with the smoothness,
affineness and connectedness assumptions supplied as instances;
`smoothConnectedAffineLocalFieldDensity` proves the displayed proposition.

The auxiliary theorem
`Langlands.AlgebraicGeometry.PointTopology.hasDenseRationalPoints_spectrum_of_separating`
is valid for any field `k` and any `k`-algebra `A` in the same universe. If
for every nonzero `a` there is an algebra map `A →ₐ[k] k` not killing `a`,
then the actual spectrum over `Spec k` has dense rational points. The proof
uses the basic opens of the prime spectrum. Every nonempty basic open has a
nonzero defining element, so separation supplies an evaluation prime in that
open. The spectrum of each algebra map is an actual rational section, since
its composite with the structure map is the identity.

For the group, take `D = Lie.coordinateAlgebra G` with its actual relative
spectrum presentation `Lie.coordinateIso G`. The published
`CharacterLatticeProof.isDomain_coord` makes `D` a domain from smoothness,
connectedness and affineness. The coordinate spectrum is smooth over `F`,
since it is isomorphic over `Spec F` to `G`. The spectrum/ring equivalence
for smoothness therefore gives `Algebra.Smooth F D`. The augmentation
`Lie.coordinateOrigin G` is an algebra point. The published
`RationalCenterComparisonProof.exists_algHom_apply_ne_zero_of_localField`
now separates nonzero elements of `D`. This theorem internally supplies a
complete nontrivial norm from the local-field structure and invokes the
implicit-function-theorem argument of
`Langlands.RingTheory.LocalFieldDensity.exists_algHom_apply_ne_zero`.
The spectrum separation theorem gives density, which descends along the
surjective coordinate isomorphism to the original group scheme.

This proof reuses published local analytic separation and actual coordinate
interfaces. It does not assert rational-point density over every infinite
field, construct a unirational parametrization, or prove spectral boundedness.
The local-field density conclusion supplies the remaining density input for
that separate spectral argument. No external literature assertion is used
as an unproved premise in this derived adapter.
