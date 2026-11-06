# Support images for the represented-parabolic geometric lemma

This module constructs the natural support-image filtration on the exact
normalized induction–Jacquet functor of the represented-parabolic geometric
lemma. It follows the support-filtration step of Renard, *Représentations des
groupes réductifs p-adiques*, 2026 version, VI.5.1, printed pp.163–164 / PDF
pp.169–170. The construction is internal, reusing the Library's
`OrderedDoubleCosets.rawSmoothSupportFiltration` and
`CorrectedFiltration.jacquetImage`.

The input is two represented parabolics with the hypotheses of the published
target and an ordered finite double-coset cover `s` of their actual rational
point images. There is no assumption about a representation's dimension,
length, admissibility or irreducibility.

`leviInducingFunctor` pulls a smooth representation of `M(F)` back to the
literal Levi image, inflates it along the semidirect Levi projection and
twists by the positive half Haar modulus. Precomposing the existing smooth
support filtration with this functor gives `leviInductionSupportFiltration`.
Its ambient functor is the actual normalized induction restricted to
`Q(F)`.

`leviJacquetImageSubfunctor` takes the image of each support submodule
under the quotient map to the actual radical coinvariants. The normalized
Levi action preserves this image because it is a scalar multiple of the
descended action. Pullback along `leviPointsEquiv` makes this an
`L(F)`-subrepresentation. Intertwiners preserve these images because their
maps on coinvariants are induced by the original maps.

`leviJacquetSupportFiltration` assembles those subfunctors into a filtration
of the published `leviJacquetInductionFunctor`, at independent universes `u`
and `v`. Monotonicity follows from containment of the original support
submodules. The zero endpoint is the image of zero, and the final endpoint
is all coinvariants because the quotient map is surjective.

This module constructs no orbit ordering or intersection datum. It does
not identify the successive quotients with geometric-piece functors.
Those identifications are the remaining normalized comparison in
Renard VI.5.1.
