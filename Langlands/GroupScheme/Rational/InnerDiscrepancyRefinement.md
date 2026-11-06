# Fpqc reflection of inner discrepancy

This internal extension of the local group isomorphism interfaces proves
that inner discrepancy for a faithful action can be checked after an fpqc
refinement of its parameter cover. The base is an arbitrary scheme, and all
schemes lie in an arbitrary universe `u`.

Let `e : LocalGroupIso G H U`, let `a` be an automorphic action of `A` on
`G`, and let `r : V → U` be a morphism in the slice over the base.
`HasInnerDiscrepancy.refine` pulls an existing representing point back along
the two refined cover points. This direction needs no hypothesis on `r`
or faithfulness of the action.

`HasInnerDiscrepancy.of_refine` assumes that `r` is quasi-compact, flat and
surjective, that `a.IsFaithful`, and that `e.refine r` has inner discrepancy.
It constructs inner discrepancy for `e`, including the representing points
on every relative test scheme and their equations after every refinement.
In particular, neither a cocycle nor its naturality or cocycle laws is
assumed as an input.

The proof first takes a representing point `δ` on `V × V` for the universal
pair of refined cover points. If two maps to `V × V` have the same image in
`U × U`, the pullbacks of `δ` represent the same discrepancy of `e`.
Faithfulness and the published uniqueness theorem make these pullbacks
equal. The product refinement `r × r` is an effective epimorphism, so
`EffectiveEpi.desc` descends `δ` to an actual morphism `δ₀ : U × U → A`.
Epimorphic cancellation verifies its structure map and recovers `δ`.

The discrepancy equation for `δ₀` is tested on `(U × U) × G`. Its pullback
along `(r × r) × id_G` is the given discrepancy equation for `δ`, by
naturality of the local isomorphisms and of the action. Products preserve the
three fpqc properties, so this morphism is an epimorphism. Cancellation
therefore proves the universal equation before refinement. The published
overlap theorem then supplies innerness on all relative tests.
`hasInnerDiscrepancy_refine_iff` combines the two directions.

`innerCocycle_refine` proves that the canonical natural discrepancy cocycle
commutes with every cover refinement. Both sides have the refined
discrepancy equation, so the published uniqueness theorem identifies them.
This equality needs faithfulness and innerness for `e`, but no fpqc
hypothesis on the refinement.

`innerCocycleOfRefinement` is the actual construction selected by this
definition contribution. Given a faithful action, an fpqc refinement `r`
and innerness of `e.refine r`, it applies the reflection theorem and then
the published canonical cocycle construction to produce `Cocycle A U`.
Its discrepancy theorem proves the equation for the original local
family. Its refinement theorem identifies its pullback with the canonical
cocycle of `e.refine r`. No cocycle is required as input: its naturality,
identity and cocycle laws are included in the constructed object.

The provenance is internal: the module combines the published local-family
refinement, all-test uniqueness, universal overlap and cocycle construction
interfaces with Mathlib's effective epimorphism and fpqc property APIs.
For a supplied actual adjoint quotient its inner action has the required
faithfulness by the published theorem. The result can descend innerness
established after a larger field cover to a chosen finite field cover.
It does not construct a quasi-split model, adjoint quotient, initial local
isomorphism, or its innerness after extension, and it does not prove the
quasi-split inner-form existence statement.
