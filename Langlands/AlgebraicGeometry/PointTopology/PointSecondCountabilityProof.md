# Finite coordinates and a finite affine cover prove second countability

This proves `Langlands.AlgebraicGeometry.PointTopology.PointSecondCountabilityStatement`
for every commutative base R and second-countable topological value R-algebra S,
in an arbitrary common universe. The proof retains the statement's precise
topologies and hypotheses.

`affineAlgebraPointSecondCountability` chooses a surjection from a polynomial
R-algebra on `Fin n` to the given finite-type algebra. The already proved
`AlgPoint.isEmbedding_precomp_of_surjective` embeds its actual algebra-map
points in polynomial points. Composing with
`AlgPoint.polynomialPointHomeomorph` embeds them in `Fin n → S`, with its
product topology. This finite power is second countable. Mathlib's embedding
transfer supplies second countability of the source, without Hausdorffness.

`affineSchemePointSecondCountability` applies this result to the actual
coordinate algebra `AffineCoordinateRing R X`, whose finite type is already
proved from affineness and local finite type of the structure morphism.
`affineSchemePointHomeomorph` transfers the result to actual relative scheme
points in their existing affine topology.

`schemePointSecondCountability` assumes the additional local-ring and
`IsOpenUnits` hypotheses. Quasi-compactness of the structure map over the
affine base makes the scheme quasi-compact. Mathlib extracts a finite affine
open cover C. Each chart inherits local finite type and has the affine
second-countability instance just proved. The proof forms their dependent
disjoint union, with each chart's affine topology. Its finite index makes
this sum second countable.

The map from that sum to actual X-points is `openPointMap` on each component.
For surjectivity, the proof chooses a chart containing the image of the closed
point of Spec S. `range_subset_open_iff_closedPoint` gives containment of
the whole image, and `openPointLift` supplies the actual factorization.
Continuity is the defining chart-continuity property of `schemePointTopology`.
Openness follows from the published `isOpenEmbedding_schemeAffineChart`,
which uses locality, open units and continuous inversion. The sum map is
therefore an open quotient map. Mathlib's
`IsOpenQuotientMap.secondCountableTopology` proves second countability for
exactly `schemePointTopology R X S`.

Finally `pointSecondCountability` assembles these three results. No
separatedness, Hausdorffness or local-compactness assumption enters the proof.
The finite cover uses the target's quasi-compactness premise explicitly.
This supplies the local prerequisite only; arithmetic and adelic applications
are separate results. The target documents the derivation from Conrad's
Propositions 2.1 and 3.1 and its use in Section 4.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp.2 and 4, Propositions 2.1 and 3.1,
and printed p.9, Section 4. It is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The local second-countability assertion is derived from these constructions;
it is not a verbatim theorem of the paper. No topology on the base ring R
is used.
