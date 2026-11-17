# Compact acyclicity of analytic étale point products

This internal specialization applies `Cohomology.PointProductAcyclic` to the
actual family `etalePoints L h` on the étale site of the analytic space `X`.
The coefficients are arbitrary modules over the displayed commutative ring,
presented either as a discrete diagram or as an independent family indexed by
`L`-valued points of `X`.

`etalePointProductInjectiveResolution` supplies an actual injective resolution of
the resulting product of point skyscraper sheaves. It specializes the resolution
obtained by resolving the coefficient diagram and applying the exact,
injective-preserving point-product functor. The required local smallness and
sheafification instances are the existing analytic étale ones.

`isZero_etaleCompactCohomology_coefficientPointProduct` and its family version
`isZero_etaleCompactCohomology_pointProduct` prove that the existing
`etaleCompactCohomology L h R (q + 1)` is zero on each such product. Their support
convention is exactly the existing topology `pointTopology L X`, with sections
evaluated at `etaleSelf X`. The proofs install the established enough-injectives
instance for analytic étale module sheaves and apply generic compact-derived
vanishing. No Hausdorffness, surjectivity of `pointProjection`, or injectivity
of the module coefficients is required.

The result concerns ordinary products of point skyscrapers on the plain étale
site. The locally discrete coreflector in the equivariant Godement construction
requires a further acyclicity argument. This module does not establish that
remaining restricted equivariant Godement assertion.
