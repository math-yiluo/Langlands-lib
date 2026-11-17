# Ordinary compact acyclicity reduced to the general c-soft theorem

The setup is the one in `AnalyticSmoothPointProductCSoft`: a complete
ultrametric normed base field `K : Type u`, a normed extension `L : Type uL`,
an actual `X : LocalizedCategory.{u, v, v}`, supplied point axioms for every
`L`-valued point, and an action `ρ` of a topological group `G : Type z` by
analytic automorphisms. For `W = max u (v + 1) uL`, the group is `W`-small,
the distinguished lift system has admissible refinements, the commutative ring
`R` belongs to `Type W`, and its module coefficients are arbitrary independent
objects indexed by the lifted actual point family.

This module specializes the actual universe-transport cohomology isomorphism
to the existing restricted locally discrete analytic point product. The native
ordinary sheaf on the lifted space has already been proved c-soft, for arbitrary
independent coefficients and all original universes, when the underlying space
is Hausdorff and `IsContinuousAction ρ` holds.

Under these same Hausdorffness and analytic continuity hypotheses, the ordinary
compact-acyclicity conclusion is reduced to the
Library proposition `CSoftAcyclicityStatement` in the coefficient universe.
That general c-soft acyclicity theorem is an explicit premise, not supplied
data or a theorem asserted here. Local compactness of the actual analytic
space and its canonical lift is proved by the preceding geometric result.

The last theorem additionally assumes surjectivity of `pointProjection L X`
and an explicit vanishing premise for every positive ordinary higher direct
image of the actual smooth product. It combines these with the ordinary
conclusion using the constructed supported derived comparison. Thus it makes
precise the two remaining mathematical inputs and does not assert that the
analytic étale compact-acyclicity target is already proved.
