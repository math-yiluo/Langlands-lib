# Original incident facets realizing arbitrary cocharacter supports

For any integral cocharacter `μ` of the actual maximal split torus, the
definition `incidentFacetOfCocharacter B x hfinite μ` constructs an original full
affine-root facet incident above the facet of `x`. The assumption `hfinite`
requires finite root separation from `x` to every point of the apartment.
Supplied apartment axioms imply this assumption.

The definition projects `1 ⊗ μ` to the actual translation space, takes its facet
for the actual derivative arrangement of the roots through `x`, and applies
the inverse of `incidentFacetDerivativeOrderIso`. The inverse law proves that
the resulting original facet has exactly this derivative facet. No replacement
of original incidence by a new relation is made.

The chosen cocharacter `incidentFacetCocharacter` for this original facet and
the initially supplied `μ` have the same pairing signs for every actual
derivative character of the base facet. Indeed, the chosen projected vector
belongs to the same derivative sign facet as the supplied projected vector.
Evaluation of each actual root form at a pure tensor is the real cast of its
integer pairing. The resulting sign equality includes zero pairings.

Consequently `incidentFacetRootSupport` of the constructed original facet is
exactly the set of base-facet derivative characters with nonnegative integer
pairing on `μ`. The final theorem supplies such a facet under the apartment
axioms for every integral cocharacter. All results are uniform in universe `u`.

This is an internal consequence of the existing derivative-facet equivalence,
actual derivative-root identification and integral representative construction.
It establishes realization of cocharacter supports in a single apartment.
It does not identify an actual model image with a dynamic parabolic or construct
the global special-fibre parabolic bijection.
