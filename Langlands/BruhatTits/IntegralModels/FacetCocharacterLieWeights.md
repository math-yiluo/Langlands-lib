# Integral cocharacter supports from supplied facet Lie-weight formulas

This internal adapter specializes the existing genuine integral cocharacter
`incidentFacetCocharacter B F` to the special fibre of a supplied integral split
torus. The definition `IntegralTorusData.incidentFacetSpecialCocharacter` uses
`cocharacterSpecialization` of that same torus. Its pairing formula uses the
inverse of `characterSpecialization`, so the character and cocharacter maps
preserve the actual integer pairing. The generic torus inclusion may be
conjugated, as in the translated-apartment sign clause.

For an original incident full facet `F` above the facet of `x`, assume the actual
model morphism satisfies `HasApartmentLieWeightSignFormula` on these two sets.
Also assume finiteness of the roots separating `x` from the point obtained by
translating it by the projected integral cocharacter. The theorem
`nonzeroLieImageWeights_eq_incidentFacetSpecialCocharacter` identifies the
actual nonzero differential-image weights of the model's schematic image in
the supplied quotient with its actual relative roots having nonnegative
integer pairing with the specialized cocharacter. The apartment-axiom version
discharges this individual finite-segment assumption. The final theorem accepts
the original-apartment `HasLieWeightSignFormula` instead.

The proof substitutes `incidentFacetCocharacterRayVector` in the supplied sign
formula at `x`. Its projected translate belongs to the original `F`, by the
prescribed positive-ray construction. Evaluation has the same nonnegativity as
the original integral pairing, because the ray parameter is strictly positive.
Pairing specialization then gives the formula in the actual special-fibre
lattice. All assertions are uniform in universe `u`.

If the actual quotient roots are additionally identified with the specialized
derivative characters of the base facet, the preimage of these Lie-image
weights under `characterSpecialization` equals `incidentFacetRootSupport B F`.
This follows by the integral formula, pairing compatibility and injectivity of
the character equivalence. This last theorem retains that root identification
as an explicit hypothesis.

The results are derived from the existing sign clauses, positive-ray geometry
and integral-torus lattice compatibility. They do not prove that an actual
model satisfies a sign clause or the root identification. They do not deduce
equality of subgroup schemes from equality of Lie supports, construct a
parabolic bijection, or prove the exact unramified parabolic-order target.
