# Unconditional linearity of original canonical face quotient comparisons

This internal construction for the finite vector-bundle filtrations of
supplied relative radicals proves linearity of the ORIGINAL
actual `sameParabolicQuotientIso` over an arbitrary nontrivial commutative
ring at universe `u`. The final interface has no supplied coordinate
conjugator, coefficient chart, scalar-equivariance or linear-transition
premise.

The inputs are an affine reductive actual group `G`, two fibrewise maximal
split tori with finite coordinate types, their actual fibrewise root data
and actual root parametrizations, and supplied split parabolic face charts
`C` and `D`. Their original actual contracting subgroup functors agree,
and their original actual parabolic subgroup functors agree. These are
the exact geometric equalities supplied to the existing canonical
comparison. The original cocharacters need not be regular. The two exact
layers use their own index types. Their ranks agree by specializing the
resulting linear equivalence to a residue field of `R`. Both may be zero.

`VectorGroup.coefficientMap` is the actual base-changed vector morphism,
preceded by the inverse source and followed by the target canonical
standard vector-group base-change isomorphism. Its `_fac` theorem proves
the actual commuting square.
`pullback_isEquivariant_of_coefficientMap` transfers an equivariance
equation in these standard coordinates back to the original actual
pullback morphism using the equivariance of the two canonical vector
isomorphisms. The `_affine` variant retains any specified affine
projection, using the proved equality of that projection with `Spec.map`
of its coefficient map. These are equalities of actual morphisms and
actions rather than replacement point functions.

`FppfQuotientComparison.coefficientQuotient_fac` proves that coefficient
extension preserves an actual commuting vector-quotient square.
`AutomorphicAction.isEquivariant_of_iso_square` transfers equivariance
back through two equivariant actual isomorphisms and an actual square;
its proof cancels the target isomorphism on each scheme test.

The original-to-fresh term comparisons from `SplitFaceQuotientBaseChange`
are compatible with the canonical original comparison:
`sameParabolicTermIso_affineBaseChange_square` proves the actual square by
cancelling the fresh target ambient representing inclusion and applying
the original and base-changed ambient equations.
`sameParabolicQuotientIso_affineBaseChange_square` proves the corresponding
square on the actual standard vector quotients, by full fppf quotient
`hom_ext` and the actual quotient-map factorizations.
The fresh charts in these intermediate lemmas are arbitrary independently
chosen charts on the pulled-back roots. The canonical original quotient
morphism is retained in the coefficient square.

`coefficientMap_sameParabolicQuotientIso_isEquivariant` applies on a
coefficient neighborhood with an actual original-parabolic coordinate
conjugator. The actual original parabolic representative lifts that
conjugator to a base point of its group scheme. The previously proved
coordinate-conjugacy theorem gives a positive scalar weight for the
fresh actual canonical comparison, hence all scalar powers by its actual
matrix formula. The two original-to-fresh quotient isomorphisms likewise
commute with every scalar power. The actual quotient square and
`isEquivariant_of_iso_square` therefore prove all-power equivariance of
the original coefficient map.

`coefficientMap_sameParabolicQuotientIso_isEquivariant_of_conjugacy`
derives every geometric coefficient input for that calculation:
reductivity and affine geometry of the actual pulled-back ambient group;
fibrewise maximality of the actual coordinate base-changed tori; the
actual pulled-back fibrewise root data and root parametrizations; and
existence of independent fresh face charts. The actual cocharacter
base-change theorem and dynamic base-change comparisons transport the
given original contracting and parabolic equalities. No such equality,
chart or root datum over the new coefficient ring is separately assumed.
The `_affine_conjugacy` variant performs the same argument for an
arbitrary specified affine projection, by installing the induced
coefficient-algebra structure and transporting the entire dependent
statement along the actual projection equality.

The generic
`AutomorphicAction.isEquivariant_of_etale_coefficientChange` reflects
actual multiplicative-group equivariance along any étale cover of the
base. For each arbitrary test scheme it pulls back that cover, lifts both
the acting point and the target point through the actual base-change
point equivalences, and identifies the pulled-back acting group with the
standard `Gm`. Naturality and the local equations give equality after
each covering map. The represented fppf sheaf property makes this étale
cover an effective epimorphic family, whose `hom_ext` proves equality
on the original test. There is no finite-cover, reduced-test or
global-point-lift assumption.

`sameParabolicQuotientIso_isEquivariant_power` constructs the actual
étale coordinate-conjugacy neighborhood at every base point using
`etaleParabolicCoordinateConjugacyAt`. These neighborhoods form an
étale cover of the original affine base. Each coefficient ring is
nontrivial because the neighborhood contains a specified point. The
derived affine-neighborhood theorem proves the standard coefficient
equation there; the pullback comparison and effective-epimorphic
reflection prove actual scalar equivariance of the ORIGINAL canonical
comparison for every natural power `N`, including zero.

`sameParabolicQuotientIso_hasScalarWeight` specializes to `N=1` and
derives the all-coefficient-algebra weight identity.
`sameParabolicLayerLinearEquiv` constructs the linear equivalence on
every coefficient algebra, keeping its actual original point function
and inverse.
`sameParabolicQuotientIso_eq_matrixHom` identifies the original actual
quotient morphism with its base-ring matrix morphism.
`coordinates_sameParabolicQuotientIso` gives that same matrix formula on
EVERY scheme test, with entries pulled back by the actual scalar map.
Nonreduced tests and empty layers are included.

The provenance is internal: actual base-change maps and actions, full fppf
quotient uniqueness, proved original-to-fresh quotient linearity, actual
étale parabolic coordinate conjugacy, represented-sheaf equality
reflection and arbitrary-ring positive scalar rigidity. The result
closes the transition-linearity obligation for these original canonical
face quotient comparisons. Module cocycle construction, effective
vector-bundle descent and the final finite filtration statement remain
separate steps.
