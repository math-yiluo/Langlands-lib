# Proof of nonaffine scheme-model morphism descent

The theorem `SchemeLimitModel.modelMorphismDescent` proves exactly the
proposition `SchemeLimitModel.ModelMorphismDescent`, with its arbitrary
common universe and all three separate hypothesis groups. The target
is the factorization, eventual equality, and prescribed-isomorphism
portion of Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(1),(3), in the derived
cofiltered affine-base formulation explained in the statement Markdown.

The proof uses Mathlib's affine-transition scheme limit theorems. It does
not assume either model or the fixed base `S` affine, and introduces no
separatedness assumption. Its helper identifies every transition of the
source model pullback diagram as a base change of the original affine
base transition, using pullback pasting and cancellation. Affineness of
those transitions follows by stability under base change. Compactness
and quasi-separatedness of the model stages follow by base change from
the respective source morphism properties, since the base stages are
affine. The supplied cone remains limiting under base change by the
existing `TargetLimit.isLimitCone` construction.

`exists_level_morphism` composes the actual limit morphism with the
projection to the fixed target model. Its equation over `S` follows
from the given relative equation and the pullback relation. Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` factors this
map through a source model stage, retaining the equation over `S`.
A pullback lift reconstructs the actual morphism over that base stage.
Equality of its two projections proves that its `toLimit` is precisely
the original morphism. The source needs quasi-compactness and
quasi-separatedness, and the target needs local finite presentation.

`eventually_equal` instead applies Mathlib's
`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` to the two
stage morphisms followed by the projections to the fixed target model.
The assumed `toLimit` equality gives the required equality of limit
maps. The theorem supplies arrows from a common level at which the
maps to the fixed target agree. Pullback extensionality and the
`restrict` projection formulas then give equality of the actual
restricted relative morphisms. This argument requires only source
quasi-compactness and target local finite type.

`exists_level_isomorphism` first factors the prescribed limit
isomorphism and its inverse, including both equations over the limit
base. Cofilteredness puts these morphisms over one common stage.
Private identity and composition helpers prove that `restrict` and
`toLimit` preserve actual morphism identities and compositions. Thus
the two composites become identities at the limit. Applying eventual
equality separately to these two inverse equations gives stages where
they hold. A cofiltered cospan puts both equations at one further
stage with the same map to the initial common stage. The two restricted
morphisms there are inverse to one another and define the desired
actual stage isomorphism. Compatibility of `toLimit` with restriction
preserves the prescribed original morphism, rather than just producing
an unspecified isomorphism of the limit objects.

The final theorem installs each clause's explicit hypotheses locally
and combines these three results. The eventual uniqueness discussed in
the statement Markdown is not a separate theorem here; a consumer obtains
it by applying the equality clause to the underlying maps of two
descended isomorphisms. No new axioms or assumed descent fields are
used; inspection reports only `propext`, `Classical.choice` and
`Quot.sound`. Initial model existence,
property descent, explicit set-colimit and spectral adapters,
arithmetic realizations, topology, and whole-paper completion remain
separate obligations.
