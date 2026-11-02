# A common fixed point for a bounded-set stabilizer

This module proves the exact target
`Langlands.Geometry.Metric.KP.BoundedSetStabilizerFixedPointStatement` from
`KPFixedPointStatement`, in every carrier universe. Its theorem is
`Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint`.

The normative source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
Theorem 1.1.15(2), printed p.6 / PDF p.37, with Definition 1.1.14 on the
same page. SHA-256:
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, Section 1.1, PDF pp.1–2, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
restore nonempty convexity and the geodesic ambient hypothesis in the hull
construction and repair the barycenter proof. These source passages were read;
the registered copies are under
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.

The source reduces the assertion to the barycenter of the closed convex hull.
The Lean proof uses the actual `closedGeodesicConvexHull` specified in
`KPDefinitions`, the intersection of all closed bounded nonempty geodesically
convex supersets. The imported `closedConvexHull` theorem from `KPClosedConvexHullProof`
(in namespace `Langlands.Geometry.Metric.KP`) proves that this hull is itself
closed, bounded and nonempty convex for the input under consideration. The
`barycenter` theorem from `KPBarycenterProof`, in that same namespace, supplies
its unique barycenter and its invariance under preserving isometries.

The covariance step is proved in this module rather than assumed. An isometry
maps each normalized geodesic to a normalized geodesic, so inverse images
under surjective isometries preserve the nonempty convexity predicate.
Continuity preserves closedness under inverse image, and the isometry's
inverse distance bound preserves boundedness. Pull back every defining
closed bounded convex superset of `e '' M`. The intersection's universal
property gives

`e '' closedGeodesicConvexHull M ⊆ closedGeodesicConvexHull (e '' M)`.

Apply the same inclusion to `e.symm` and cancel the inverse maps for equality.
This helper equality is unconditional for sets in a metric space, since it
compares the defining families directly, including the case of an empty
family. In the final theorem the imported hull result supplies all required
existence and boundedness facts. Every isometry preserving `M` therefore
preserves this one hull, and hence fixes its one barycenter.

The resulting point is chosen before all the preserving isometries. The
original set only needs to be nonempty and bounded; the conclusion imposes
no membership in that original set. No properness, dimension, local
compactness or positive-radius hypothesis is added. The covariance helpers
are elementary derived results, and no external Lean code is adopted.
