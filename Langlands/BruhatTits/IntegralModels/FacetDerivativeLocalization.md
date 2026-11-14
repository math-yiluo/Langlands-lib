# Actual facet derivative roots and integral cocharacter representatives

This module gives the actual-character specialization of the derivative
localization comparison. The field and actual supplied building data retain
arbitrary universe `u`.

`mem_facetDerivativeRoots_facet_iff` identifies the existing actual-character
predicate `facetDerivativeRoots B (facet B.affineRoots x)` with membership of
`rootForm B.i a` in the derivative image of affine roots through `x`.
`image_rootForm_facetDerivativeRoots` identifies that whole image. These are
internal consequences of the definitions: roots through `x` vanish on its full
facet, and every actual affine root has the form of an actual relative root as
its derivative. No apartment-axiom or affine-root-system premise is needed.

`exists_cocharacter_mem_derivativeFacet` realizes every full facet of the actual
derivative arrangement by the projection of `1 ⊗ μ` for a genuine integral
cocharacter of the original torus. The proof lifts a real representative from
the reduced translation-space quotient, uses finiteness of actual relative
roots for the supplied maximal split torus in a smooth connected reductive
group, and applies `RealTorusSpace.exists_cocharacter_sign_eq_on_finite`. The
identities `rootForm_mk` and `eval_tmul` show that the projected integral vector
has the same signs for every derivative form. `derivativeFacetCocharacter`
chooses such a representative, with its membership theorem.
`incidentFacetCocharacter` specializes this choice to the derivative facet of
an original incident affine facet.

This module concerns actual characters and derivative facets. It makes no
assertion that a small positive cocharacter ray reaches the original affine
facet, or that a special-fibre model image is parabolic. The construction is
internally derived from the named existing Lean APIs; it has no new reliance
on original literature.
