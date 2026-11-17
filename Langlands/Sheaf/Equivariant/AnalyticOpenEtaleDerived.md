# Injectives for ordinary direct image from the analytic étale site

This internal prerequisite studies the actual direct image from the analytic
étale site to the ordinary topology constructed in
`AnalyticOpenEtaleRestriction`. It does not concern equivariant restriction.

The left adjoint is the existing presheaf left Kan extension followed by
sheafification. Before sheafification, evaluation of the presheaf left Kan
extension at an étale object is the colimit over ordinary open-domain
factorizations. Representable flatness of `openEtaleFunctor` makes this indexing
category filtered. Exactness of filtered colimits of modules therefore proves
left exactness of the presheaf left Kan extension. The proof adapts
Mathlib's `lanEvaluationIsoColim` and `lan_preservesFiniteLimits_of_flat` to
retain the independent site and coefficient universe levels.

Sheafification is a separate left exact step; the raw colimit formula above
does not assert the value of the sheafified inverse image. The composite
inverse-image left adjoint is left exact. Its preservation of monomorphisms
implies that the right adjoint
`etaleUnderlyingSheaf` preserves injective objects. This is the ordinary/étale
site adjunction; no preservation-of-injectives claim is made for restriction
from equivariant or locally discrete sheaves.

All constructions are internal applications of existing Library and Mathlib
Kan-extension, sheafification, filtered-colimit and adjunction theorems. Higher
direct-image vanishing on the special Godement terms remains an additional
obligation.
