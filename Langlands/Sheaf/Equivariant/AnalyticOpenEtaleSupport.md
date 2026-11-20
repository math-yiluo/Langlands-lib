# Ordinary-open germs and analytic étale support

This internal prerequisite identifies global sections and their actual germ
supports after ordinary-topology restriction. It retains independent analytic
space, field and coefficient universes.

The canonical open domain for the whole space is isomorphic to the identity
étale object. Applying a sheaf gives `etaleUnderlyingGlobalIso`, and its
ordinary restrictions are the original étale restrictions to open analytic
domains. These specialize the
[conditional global-sections comparison](AnalyticOpenEtaleRestriction/GlobalSections.md)
at the published proof of open-domain étaleness.

`underlyingTopologyPoint` is the usual point of the ordinary-open site: its
fiber over an open is the lifted proposition that the point lies in that open.
It repeats Mathlib's `Opens.pointGrothendieckTopology` construction with the
fiber lifted to the larger coefficient universe. The support used here is the
existing `PointSupport.support`, computed by actual filtered-colimit germs at
these ordinary-topology points. The local equality criterion shows that a
global section has zero ordinary germ exactly when it vanishes on an ordinary
open neighborhood.

For an étale sheaf, vanishing after restriction to an étale object descends to
its entire open image: the canonical factorization of that object through the
open analytic domain is surjective on underlying points and hence is an étale
cover. Sheaf separatedness then gives vanishing on the image.

On a Hausdorff space with surjective field-point projection, the existing
analytic support theorem characterizes the complement of the underlying étale
support by vanishing on an étale neighborhood. Passing to the open image and
using the ordinary zero-germ criterion proves
`support_etaleUnderlyingGlobalIso`. Conversely, an ordinary open domain is
itself an étale neighborhood, giving the reverse inclusion.

`underlyingTopologyCompactSections` applies the existing
`PointSupport.sheafCompactSections` to the ordinary site with these standard
points. It therefore uses actual ordinary point germs and compact bounds in
the original underlying space; it does not introduce a replacement support
predicate. The section is compactly supported in this ordinary sense exactly
when the original étale section is compactly supported in the existing induced
topology on field-valued points. This follows from the support equality and the
published compact-bound equivalence for the surjective field-point projection.

`etaleUnderlyingCompactMap` restricts the actual global comparison to these
compact submodules, and naturality is the original sheaf morphism's naturality
on the full-domain arrow. The global linear equivalence preserves and reflects
the two compact predicates, so this map is invertible.
`etaleUnderlyingCompactIso` packages the resulting natural isomorphism of the
actual degree-zero compact-section functors.

This uses existing Library domain, étale openness, point lifting and support
theorems and Mathlib's equality-of-germs criterion, with no new literature
assertion. It does not yet compare right-derived compact sections or prove
local absolute-Galois acyclicity.
