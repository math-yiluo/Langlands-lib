# Actual integral cocharacter rays in incident facets

This internally derived adapter uses the existing building `B`, its actual
torus `B.S`, and the genuine integral `incidentFacetCocharacter B F` attached to
an original full facet `F` incident above the facet of `x`. All fields and group
schemes have arbitrary universe `u`.

Assume finite root separation on the segment from `x` to the translate by the
projection of `1 ⊗ incidentFacetCocharacter B F`.
`eventually_pos_cocharacterRay_mem` proves that every sufficiently small
positive scalar `t` makes the projection of
`t ⊗ incidentFacetCocharacter B F`, translated by `x`, belong to the original
`F`. This follows from membership of the projected integral representative in
the actual derivative facet and the prescribed-ray theorem in
`AffineIncidentFacetRay`. Compatibility of the quotient map with scalar
multiplication identifies its vector ray with this tensor ray.

`incidentFacetCocharacterRayParameter` chooses a scalar strictly between zero
and one, and its specification retains both inequalities and original-facet
membership. `incidentFacetCocharacterRayVector` is the resulting actual real
cocharacter tensor. `incidentFacetCocharacterRayVector_mem` is its projected
membership specification.

For every actual character of `B.S`, including characters outside the root
set, `sign_eval_incidentFacetCocharacterRayVector` identifies its sign on this
real vector with the sign of its integer pairing with the chosen integral
cocharacter. The evaluation formula for pure tensors gives the positive real
scalar times that integer. The corresponding nonnegativity equivalence is
`eval_incidentFacetCocharacterRayVector_nonneg_iff`.

`exists_pos_cocharacterRay_mem_of_apartmentAxioms` supplies the finite-segment
premise from the given apartment axioms via their rank-zero-compatible affine
root-system property. The other constructions require only the stated
finite-segment premise; no positive-rank condition is imposed.

The provenance is internal: this is a specialization of the previous
derivative-facet representative and prescribed-ray constructions, using the
existing tensor evaluation and quotient maps. It supplies a usable vector for
a facet Lie-weight sign formula. It does not prove that formula for integral
models or assert a special-fibre parabolic correspondence.
