# Apartment-compatible descent from fixed restriction data

`UnramifiedBuildingDescent.ApartmentDescentData B` is an internal witness
structure recording exactly the eight conclusions of
`UnramifiedApartmentDescentStatement` for the supplied datum `B`. Its fields
are the upper building, its semilinear action, a building map, an affine
apartment map, and the eight required properties. It imposes no new
restrictions on the original target statement.

The conditional construction `apartmentDescentData` assembles this witness
using the existing `descentMap` and the affine `descentAffineMap`. It retains
the explicit hypotheses needed by those constructions: an upper apartment
and compatible centralizer, a carrier comparison with the fixed upper
apartment, uniqueness of restriction on fixed points, normalizer transport,
root-filtration comparison, upper apartment injectivity, a lower building
axiom and rational orbit representatives for fixed upper building points.
The lower torus inclusion must factor through the original upper torus.

One further hypothesis identifies the actual lower affine roots with the
nonconstant restrictions of the actual upper affine roots along
`descentAffineMap`. It supplies both the facet and special-point clauses:

- `descentAffineMap_facets` applies the general preimage formula for the facets
  of a restricted affine arrangement.
- `descentAffineMap_isSpecialPoint` first reflects specialness of the upper
  apartment image to specialness in its apartment, then applies special-point
  descent for nonconstant root restriction. Upper root derivatives are nonzero
  because the upper torus is split. No building axiom is needed for this step.

The building injection, equivariance, apartment compatibility and fixed-point
surjectivity come from the published quotient descent lemmas. Coefficient
fixedness and torus-unit fixation come from `UnramifiedDescentFixedImage`.
The special-point clause follows by uniqueness of fixed lifts and the
apartment special-point result above. This replaces a separate
special-point-descent hypothesis with the same actual-root restriction
identity already used for the facet clause.

This is a derived assembly of Library constructions and their proved formal
consequences. It does not establish existence of its input data or prove the
unconditional target statement. In particular, the actual affine-root
restriction identity remains a hypothesis and is stronger than the
published comparison of root directions alone.
