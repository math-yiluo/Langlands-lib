# Fixed image and torus units for the unramified descent map

This internal consequence of the published quotient descent construction proves
two clauses needed for `UnramifiedApartmentDescentStatement`. The carrier,
fixed-lift uniqueness, normalizer compatibility and root-filtration hypotheses
of `UnramifiedBuildingDescent.descentMap` remain explicit premises. In addition,
`descentMap_fixed` assumes that the predicate used to choose lifts implies
fixedness under the actual coefficient action on root-function families.

Every lower building point is a rational group translate of an apartment point.
The descent map is equivariant and agrees with `descentPoint` on apartments.
The semilinear action on the upper building agrees with the existing Galois
quotient action. Semilinearity, fixedness of scalar-extended rational points
and fixedness of the chosen apartment lift then show that the descended point
is fixed. `fixedDescentMap` restricts the codomain of this same map to the
subtype of coefficient-fixed building points; it does not claim surjectivity.

For `descentMap_torusUnits`, a factorization of the lower torus inclusion
through the original upper torus is supplied. The published
`isFixedByScalarTorusUnits_apartmentMap` puts every bounded scalar-extended
lower torus point in the fixer of every upper apartment point by the V6
centralizer compatibility. Applying it to the chosen lift and rewriting the
torus factorization and `descentMap_apartment` gives the torus-unit clause.
This clause needs neither the extra fixedness hypothesis nor Galois stability.

These results are derived from Library definitions and proved comparison and
fixation lemmas. They do not assert the unconditional apartment descent
statement or discharge its carrier and structural input hypotheses.
