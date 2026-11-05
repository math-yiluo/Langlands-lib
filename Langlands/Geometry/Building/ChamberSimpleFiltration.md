# Root filtrations across a chamber-simple wall

This module develops the root-filtration step in chamber-simple factorization,
using only AS 4 and the published chamber and wall geometry. It works over any
field with the supplied `KPApartmentData`, without additional building axioms.
It is a derived development from `SimpleReflectionPositivity` and
`ChamberFiltration`, motivated by the corrected proof of KP Theorem 7.5.1,
printed p.259 / PDF p.290 and the 1 November 2024 corrections, PDF p.35.

`sign_reflection_eq_of_extendedAffineRoot` extends the simple-wall sign
comparison from affine roots to extended affine roots by applying AS 4 to
the root or its positive double.

`rootFixer_le_reflected_of_not_pos_multiple` treats roots whose derivative
is outside the positive real ray of the wall derivative. A nonidentity
root element determines an extended affine root via its valuation. Its
chamber-fixer membership makes this root positive throughout the chamber.
If it were proportional to the wall root, the scalar would be positive,
contrary to the derivative condition. The sign comparison now proves
membership in the reflected chamber's root fixer.

`rootFixer_eq_affineRootGroup_of_pos_multiple` identifies the chamber fixer
on a wall ray with the filtration at the specified positive multiple of
the wall functional. The wall face contains a point in every chamber
point's sign closure. The filtration comparison at this point proves
one inclusion, and nonnegativity of the wall multiple on the chamber
proves the reverse inclusion.

`affineRootGroupPlus_le_reflected_rootFixer_of_pos_multiple` treats the
positive-depth filtration above that multiple. The valuation functional of
a nonidentity element is strictly positive at a wall point, so cannot be
proportional to the wall root. It is positive on the original chamber,
and therefore on its reflection. This also applies to the half-wall
filtration in the doubled relative-root case.

These results do not prove the full chamber product decomposition or the
exact chamber-simple parahoric factorization.
`ChamberSimpleFiltrationStatement` is the Prop-valued bundle of the three
comparisons, with AS 4 explicit, and `chamberSimpleFiltration` proves it.
Author: Worker 1647.
