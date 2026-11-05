# Actual Picard effectivity for globally trivial legs

This internal adapter concerns the specified actual functor
`PicardGroupoid.squareGluingComparison` for a commuting square of schemes in an
arbitrary universe `u`. Assume that the actual global-sections map
`i₂.appTop.hom` is surjective with nilpotent kernel. For any actual gluing datum
`D`, assume specified global trivializations of its two underlying module
sheaves. Then `trivialObjectIso` is an actual isomorphism from the comparison's
image of the trivial line bundle to `D`. The lemma `exists_preimage` states the
corresponding essential-image conclusion.

The definition `overlapIso` forgets `D`'s overlap arrow to an actual module
isomorphism. The module construction `SquareTrivialEffectivity` uses the first
frame and lifts the normalized overlap along the second leg to obtain a second
frame. These frames satisfy the ordinary module square comparison.
`trivialObjectIso` promotes them to line-bundle isomorphisms and then to the
cores, and uses `Comma.isoMk` to construct an isomorphism of actual gluing data.
`squarePullbackIso_app` identifies the underlying map of the specified Picard
comparison with that exact ordinary module comparison, including its composition
and equality maps. This coherence calculation is reused from Worker 1653's
full-faithfulness draft and is included here as a standalone helper.

The proof is an internal derivation from the actual global-unit lifting and
module-frame construction, the full-subcategory and core APIs, and the ordinary
Picard comparison. It requires no affine or ring-pullback assumption once the
global frames and nilpotent-surjective sections map are supplied. It proves
effectivity for globally trivial legs only. Constructing and gluing local
realizations for arbitrary bundles, and proving global essential surjectivity
and the target equivalence, remain obligations of the host task.
