# Actual positive-radius rational charts for finite Laurent neighborhoods

Author: Worker 84.

This internal construction turns the Library's finite Laurent inequality
neighborhoods into actual rational quotient presentations over the original
ambient algebra. It supplements the topological construction in
`Spectrum.LaurentNeighborhoods` using existing rational charts and their
all-products intersections.

`RationalChart.upperBound a r hr` uses denominator one and a chosen series
representative of the actual quotient element `a`. Its locus is exactly
`{x | x a ≤ r}`. `lowerBound a q hq` uses a representative of `a` as its
denominator, unit numerator and radius `q⁻¹`. Its locus is exactly
`{x | q ≤ x a}`. A unit appears among the coefficient classes in each case,
so unit generation holds even for zero quotient algebras. The chosen
representatives come from the surjective presentation map.

`listInter` and `finiteInter` iterate the existing rational intersection
construction, starting with the whole-spectrum chart for an empty family.
Their membership theorems identify the loci with the corresponding finite
intersections. `finiteLaurent` intersects all elementary upper and lower
charts. `locus_finiteLaurent` identifies its locus with the finite Laurent
inequality locus for arbitrary positive real thresholds.

`exists_rational_neighborhood` applies the existing finite Laurent neighborhood
theorem and replaces its locus by this actual rational chart. Thus every
neighborhood of a point of the ambient spectrum contains a rational chart
locus that remains a neighborhood of that point. This establishes a basis
for the ambient topology. It does not assert that every point of an arbitrary
full affinoid domain has a contained relative rational neighborhood, which is
the missing analytic input to the full Gerritzen–Grauert proof.

The construction follows the rational and Laurent formulas in M. Temkin,
*A new proof of the Gerritzen–Grauert theorem* (2005), registered source
`temkin-2005-gerritzen-grauert`, PDF SHA256
`1948a0be381d7dd4d4b5166c9b00f2ffa903a30a6ee0ffd09f754a5e9ad9c334`,
printed/PDF p. 8, the paragraph before Theorem 3.1. That paragraph states the
finite Laurent neighborhood basis with arbitrary positive real thresholds.
The use of chosen series representatives and the already constructed
all-products intersection is an internal implementation of these formulas.
