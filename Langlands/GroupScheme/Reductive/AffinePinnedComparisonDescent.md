# Fppf descent of actual comparisons of affine pinned models

This internal module derives a gluing interface from the published
`LocalGroupIso` constructions and fppf descent. It supports the proof of
`RelativePinnedComparisonExistenceStatement` without asserting existence of
pinned normalizations.

For a flat, surjective morphism `p : V → T` locally of finite presentation,
`comparisonToIterated` converts a comparison of the actual direct model
pullbacks over `V` into an isomorphism between the iterated pullbacks of the
models over `T`. Its formula uses `baseChangeCompIso` at both endpoints.
`comparisonLocalIso` then uses the published actual-isomorphism/local-family
equivalence to obtain its natural action on every relative test scheme.

If this family is independent of the point of the cover,
`descendComparison` is an actual comparison over `T`. The theorem
`pullComparison_descendComparison` says its normalized pullback is exactly the
input comparison, and `existsUnique_descendComparison` gives uniqueness.
`pullComparison_injective` detects equality of arbitrary comparisons after
this fppf pullback.

The general `LocalGroupIso` lemmas prove that a global isomorphism has the same
local action at every cover point, that independent fppf descent recovers
every local value, and that the ordinary pullback of the descended isomorphism
is precisely `toBaseChangeIso`. Equality of global isomorphisms is checked
on group points after the fppf projection from each pulled-back test scheme.
This proves uniqueness without any affineness or quasi-compactness hypothesis.

All results are universe polymorphic. The base, the cover, and their refinements
may be empty, disconnected, or nonaffine. Independence is a stated hypothesis;
its verification for pinned lifts and the existence of those lifts remain
separate geometric obligations. No constant based root-datum equivalence is
chosen by this module.
