# Equivariant compact sections from local vanishing

Author: Worker 13. This internal construction extends the published
moving-space section action to the actual compact-section submodule defined
by local vanishing. It preserves independent universes for the space, group,
commutative coefficient ring and module carriers.

The input is a module-valued presheaf `F` on the actual group-labelled open
category. `ordinary` forgets labelled arrows and `restrict` is its actual
whole-space restriction. `ordinary_restrict` and `vanishesNear_iff` identify
these restrictions and their zero neighborhoods with `LocalSupport`.
`globalRepresentation` is the already constructed global-section action
converted through Mathlib's action-to-representation functor.

When each spatial group operator is continuous, it transports open
neighborhoods to open neighborhoods. Equality of the two labelled composites
proves `restrict_action`. Applying this equality to a zero restriction proves
`vanishesNear_action`. The inverse group operator proves the converse,
giving `vanishesNear_action_iff`. Taking complements and using the inverse
point operator proves `support_action`: support is exactly the image of
the original support under the given group element. Continuous images of
compact sets are compact, so these original operators preserve every
compactly supported section.

`representation` restricts the existing global representation to the
entire compact-support submodule. There is no smooth-vector condition.
For a genuine natural transformation on the labelled category, the already
proved local-support containment constructs its actual map on compact
sections. Naturality at the original whole-space action arrow proves its
intertwining equation. These maps define `presheafFunctor`, and restriction
to the full equivariant sheaf category gives `functor`. The natural
`inclusion` into `globalFunctor` has the actual submodule inclusion as
each component. `globalFunctor` retains independent space and carrier
universes, as required for these constructions.

No sheaf condition is used to construct the presheaf action, support
translation or compact maps. No topology on the coefficients, joint action
continuity, compactness of the whole space, Hausdorff condition or coefficient
smoothness is assumed. The general local support agrees with the existing
stalk support in the aligned universes by the imported `LocalSupport`
comparison; no generalized stalk is constructed here.

The provenance is internal, reusing the actual `ActionOpens`, `Topological`
and `LocalSupport` constructions and pinned Mathlib subrepresentations and
compactness. The translated-neighborhood argument is the same mathematical
argument as the earlier universe-restricted `CompactSections` construction,
now applied directly to local restrictions. There is no new original-literature
assertion. Locally constant section comparison, automatic smoothness,
analytic or etale site comparison, derived functors and Harris specialization
remain separate obligations.
