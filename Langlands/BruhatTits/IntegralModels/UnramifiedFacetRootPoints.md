# Actual root-point intersections of descended facet models

This internal supporting unit concerns a parahoric building over a nonarchimedean local field and any supplied relative-component model whose unramified neutral integral points are the zero subgroup intersected with the fixer of the image of a translated apartment subset. The subset may be empty or unbounded. The building comparison is equivariant; the reverse integral-to-fixer implication also uses its injectivity. Apartment axioms put actual root points in the simply connected image.

`facetRootIntegralSections` is the subgroup of actual neutral-model integral sections whose generic point is in the root group of the conjugated torus inclusion. It does not impose a depth condition or assert that its quotient reduction survives.

`conjugated_rootPoint_mem_integralPoints_of_fixing` proves that a root point fixing the subset, after conjugation by the specified group point, is integral. Its simply connected image membership gives the unramified zero-subgroup condition. Equivariance carries its conjugated fixing condition to the upper building, and the supplied model characterization and unramified integral-point descent give integrality.

`conjugated_rootPoint_mem_integralPoints_iff` proves exact equivalence with the intrinsic apartment root fixer. For the reverse geometric implication, an integral point fixes the image subset in the upper building. Equivariance and injectivity bring this equality to the original building; cancellation of the translating group point gives fixing of the original apartment point. The existing generic-root/fixer theorem then gives depth zero at each point. The other implication uses the preceding integrality theorem and the filtration's fixing property.

`rootGroupPoints_inf_conjugatedIntegralPoints_eq_rootFixer` packages this equivalence as an equality of actual subgroups. `conjugated_affineRootGroup_le_integralPoints` proves that an entire affine depth group is integral after conjugation whenever the affine functional is nonnegative on the subset. Its depth at each point is then at least zero, so it fixes every point there. This latter result needs equivariance but not injectivity of the comparison.

The statements and proofs are derived from the existing actual root-point, simply connected image, filtration-fixer, and unramified descent interfaces. No new literature assertion is made. This unit does not identify the exact quotient root set or prove the final derivative root datum.
