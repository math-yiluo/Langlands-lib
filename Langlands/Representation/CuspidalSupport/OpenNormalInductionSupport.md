# Support of compact induction of a finite compact restriction

This internal helper concerns an open normal subgroup `N` of a locally compact
nonarchimedean group `G`. Suppose that the full restriction of a smooth complex
representation `π` has compact smooth-dual coefficients and is spanned by a
finite family of irreducible invariant subspaces.

`openNormalRestrictionCompactInduction` abbreviates the actual compact induction
of the whole restriction, on its compactly supported covariant-function carrier.
The group and original carrier universes are independent.

`openNormalFamilyProjector_fixes_compactInduction` proves that the existing
finite-family ambient projector is the identity on this compact induction.
The selected subgroup projector is natural for the subgroup unit. The projector
fixes `π`, since the finite family spans its restriction, so it also fixes every
unit vector. The coset-sum naturality identity and the unit reconstruction
identity then show that it fixes every compactly induced function.

`openNormalFamily_compactInduction_subquotient_restricted_hom` passes this
identity through an actual subquotient presentation: injectivity gives identity
action on the intermediate subrepresentation, and surjectivity gives identity
action on its quotient. The existing irreducible projector test supplies a
nonzero intertwiner from the restriction of each irreducible subquotient to the
restriction of `π`.

The proof is derived from the published finite-family projector, intrinsic
complement, actual subquotient, and open-subgroup unit and coset-sum APIs. It does
not assert the existence of the finite family, compactness of the restriction,
an unconditional inertia classification, or the full small-progenerator target.
