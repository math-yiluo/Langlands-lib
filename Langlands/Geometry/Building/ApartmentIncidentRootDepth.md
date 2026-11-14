# Actual depth witnesses for incident ordinary affine roots

This is a derived adapter for arbitrary `KPApartmentData i ω`, over a field in
any universe. The inclusion `i` is monomorphic on its underlying schemes, and
the ambient group is affine. There is no local-field, topology, characteristic,
apartment-axiom or connected-reductivity premise.

`IsRootDepthBoundary x a r g` means that the actual rational point `g` lies in
`D.filtration x a r` and lies outside the product of
`D.filtrationPlus x a r` with the **full** group `doubleRootGroupPoints i a`.
The doubled-root factor is retained when the root is multipliable. The
accompanying lemmas show that such a point lies outside each of those factors,
is not the identity, and has valuation exactly `r`.

`affineRootGroupPlus_eq_filtrationPlus` expresses the published strict affine
root membership formula in point/depth indexing, for a functional whose
derivative is the indicated actual relative root.

`exists_rootDepthBoundary_of_affineRoot` extracts a relative root `a` with
exact derivative `ψ.linear = rootForm i a`, and one nonidentity rational point
`g`. At every apartment point `x`, this same `g` is a boundary witness at depth
`ψ x` and its valuation is exactly `ψ x`. The proof extracts an element from
the noncontainment defining the published ordinary affine roots, rewrites both
filtrations at each apartment point, and uses exclusion from positive depth
to turn the lower bound into equality.

Conversely, `affineFunctional_mem_affineRoots_of_rootDepthBoundary` turns a
boundary point at `(a,x,r)` into ordinary affine-root membership for the
published `affineFunctional a x r`. With a supplied split-torus hypothesis,
`affineFunctional_mem_affineRoots_iff_exists_rootDepthBoundary` gives the
equivalence for that prescribed root. Its forward implication uses the
published `rootForm_injective_of_split` to identify the actual derivative.

`exists_rootDepthBoundary_of_incidentAffineRoot` specializes the witness to an
ordinary affine root vanishing at `x`. One actual nonidentity point has value
zero and the doubled-root boundary exclusion at every point of the full sign
facet through `x`. The facet definition forces that root to vanish throughout
the facet, so this specialization needs no AS 4 premise.

The provenance is the published `KPApartment`, `KPRootFixerPlus` and
`LeviSpecialPoint` definitions and membership lemmas. This module supplies an
elementary actual-point adapter; it states no additional source theorem and
does not construct an integral model, prove survival in a reductive quotient,
exclude zero restriction to a smaller torus, or prove stable-chamber existence.
