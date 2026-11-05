# Ambient transport of compatible parabolic root presentations

This is an internal derived adapter for normalized-exponent standard reduction.
It combines the Library's actual Lie-weight transport, ambient transport of
parabolic and maximal split-torus maps, and functoriality of dynamic subgroups.
Its provenance is these published constructions; it makes no new assertion
about the existence or independence of root presentations.

For an actual ambient group-scheme isomorphism `e : G ≅ G'`,
`ParabolicRootPresentation.compAmbientIso` sends a compatible presentation of
`p,l,a` to a compatible presentation of `p ≫ e.hom,l,a`. The actual objects
`P,M,A,T`, the Levi and split-component maps, the generic cocharacter, the
standard face and the factor `A ⟶ T` are retained. Only the torus inclusion
and the parabolic map into the ambient group are postcomposed with `e.hom`.

The proof first applies the actual Lie-weight transport with the identity
isomorphism of the acting torus. It identifies the actual simple roots and
preserves genericity. The definition of standardness then identifies every
standard cocharacter. The choice-free intersections defining standard
parabolics and Levis consequently transport on every test scheme. These are
all-test subgroup-functor equalities, including when no standard cocharacter
exists; the presentation itself supplies one cocharacter simultaneously
realizing both represented images.

Minimality is transported by choosing the represented minimal parabolic
already contained in its definition and applying the existing ambient
minimal-parabolic transport theorem. Inverse-image monotonicity gives the
required containment in the transported supplied parabolic. The original
simultaneous realization, maximality and factorization equations supply all
remaining compatibility fields.

`restrictedRoots_compAmbientIso` proves equality of the distinct restricted
simple-root vectors in the full real character space of the same `A`.
`positiveCone_compAmbientIso` and `nonnegCone_compAmbientIso` apply the
published enumeration-free finite-sum descriptions to obtain equality of the
entire root-combination cones. They retain arbitrary real coefficients and
include the empty-root, rank-zero case.

The field has arbitrary characteristic; the ambient groups are affine and
need not be split or reductive. Local finite type of both ambient groups is
required only for the cone statements. There is no topology or valuation
premise. Applying the construction to an actual inner automorphism gives
presentation and cone conjugation. No existence of standard representatives,
comparison between unrelated root presentations, exponent transport, or exact
normalized-tempered standard reduction is asserted here.
