# Actual root support of the full special fibre

This internal construction compares the actual nonzero adjoint characters of a
smooth affine group over a local domain on two field fibres, through one actual
integral split torus. It transports the published coordinate split-torus
comparison through an actual splitting isomorphism of that integral torus.

For compatible `IntegralSplitTorusData A` in a smooth integral model, the actual
generic torus and ambient group isomorphisms identify the generic roots with the
prescribed generic group roots. The canonical character specialization through
the same integral torus therefore restricts to `fullSpecialFibreRootsEquiv`, an
equivalence with the actual roots in the full special fibre.

The provenance is internal composition of `LocalRootSupportComparison`, actual
character base change, and actual Lie-weight transport. This is a comparison of
the full special fibre, which may be nonreductive. It does not identify roots of
a reductive quotient with an affine derivative subsystem or establish incident
image parabolicity or the host facet-order bijection.

The full-special-fibre torus inclusion is the shared
`IntegralSplitTorusData.specialFibreInclusion` from
[IntegralRootSpecialFibre](IntegralRootSpecialFibre.md).
