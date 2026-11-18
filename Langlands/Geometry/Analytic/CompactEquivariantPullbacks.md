# Compact continuous pullbacks from geometric inputs

This internal construction combines two explicit, still separate geometric
prerequisites. It does not prove either prerequisite or the unconditional
finite tuple-cone statement.

`quasiEtalePullbackIsLimit` turns the full localized analytic pullback property
of a site cone into its limiting property in `QuasiEtaleSite X`. For any site
test cone it takes the unique analytic lift and uses the first projection to
prove that the lift is over `X`. Factorization and uniqueness follow from the
localized universal property. There is no compactness hypothesis on test objects.

`CompactContinuousPullbackData` records a limiting site pullback, compact
Hausdorff point, continuous action, and equivariance of both full analytic
projections for specified source actions. `compactContinuousPullback` constructs
these data from `CompactQuasiEtalePullbacksStatement` and
`CompactPullbackActionContinuityStatement`, compactness of the cospan, continuous
source actions, and a compatible action on the base. The first prerequisite
supplies a cone whose underlying localized square is a pullback. The elementary
`pullbackAction` construction gives its action and projection equations. The
second prerequisite gives Berkovich continuity of this constructed action.

The field and space universes are `u,v,v` and the acting group has independent
universe `z`. The group only carries a topology. The ambient space `X` need not
be compact, Hausdorff, or carry a continuous global action. Provenance is an
internal assembly for Task 7491 using the categorical universal property; no
pointwise injectivity or action-lift uniqueness is invoked.
