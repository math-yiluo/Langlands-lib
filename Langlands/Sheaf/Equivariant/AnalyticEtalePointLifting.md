# Lifting analytic field points over prescribed underlying points

This internal derived argument isolates the geometric input to whole-site
point-fibre detection. Its final theorem is conditional on étaleness of open
domains of the base and on stability of étale arrows under open-source
restriction. These geometric premises remain explicit; this file alone does
not prove joint faithfulness under only the final target's assumptions.

First, a field point lifts into any étale object whose underlying image
contains its projection, provided the complement of that projection is itself
an étale object. The two objects generate a sieve covering the identity object.
The covering-sieve clause of the point axioms supplies a lift through one of
them. A lift through the complement contradicts naturality of the underlying
point projection. For a Hausdorff base, the singleton complement is open, so
open-domain étaleness constructs the needed complementary object. This
reuses `pointFibre_nonempty_of_complement` from `AnalyticEtaleSupport`.

For a prescribed point of an étale fibre, the fibre-isolation theorem supplies
an open source neighborhood meeting that underlying fibre only in the given
point. Open-source restriction makes the neighborhood an object of the base
étale site. The preceding lift lands in this neighborhood, and naturality of
the projection places its underlying point in the required fibre. Fibre
isolation then forces the projection to equal the prescribed point.

Finally, surjectivity of the base point projection chooses a field point over
the image of any point of an arbitrary étale object. Applying prescribed-point
lifting proves surjectivity of the projection on that object. The independent
universes for the base field, ambient spaces, and extension field are retained.
