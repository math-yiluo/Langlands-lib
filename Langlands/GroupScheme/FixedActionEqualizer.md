# The action equalizer and the all-test fixed condition

This internal helper constructs the actual action equalizer and identifies its universal factorization condition with the already published all-test fixed subgroup. It does not construct a fixed subgroup representative or prove any of the three closed-representability existence targets.

Let `H` and `G` be group schemes over an arbitrary scheme `S`, and let `a` be an `AutomorphicAction H G`. The object `a.actionEqualizer` is the equalizer in schemes over `S` of the action morphism `a.hom : H × G → G` and the projection to `G`. Its inclusion is `a.actionEqualizerInclusion`. If `G → S` is separated, Mathlib's closed-equalizer theorem gives an actual closed immersion for the underlying inclusion. No affineness, flatness, smoothness, finite type, or projectivity hypothesis is used in this helper.

The theorem `factors_actionEqualizer_iff` is the categorical universal property: a map `f : T → H × G` factors through this equalizer if and only if its composites with action and projection agree. The forward proof precomposes the equalizer equation, and the reverse proof uses `equalizer.lift`.

For a point `g : T → G`, `mem_fixedSubgroup_iff_product` tests fixedness at the universal acting point `H × T → H`. Its forward proof specializes the all-refinement definition to the refinement `H × T → T`. Its reverse proof precomposes the equality with `⟨h,b⟩ : T' → H × T` for an arbitrary refinement `b : T' → T` and arbitrary point `h : T' → H`. Thus the criterion retains every test scheme and every refinement, including nonreduced tests.

Finally, `mem_fixedSubgroup_iff_factors_actionEqualizer` combines these two equivalences. A point `g` belongs to the fixed subgroup precisely when the entire product map `H × T → H × G` induced by `g` factors through the action equalizer. This is the interface for the generic closed-factorization locus prerequisite. The equalizer is a subscheme of `H × G`; a further geometric construction is still required to obtain a closed representative inside `G`.

The provenance is internal: the object and factorization theorem use the categorical equalizer, its closed immersion uses Mathlib's `isClosedImmersion_equalizer_ι_left`, and the product criterion unfolds the published `AutomorphicAction.IsFixed`. These are intrinsic comparisons of existing definitions.
