# Relative flatness descent

This internal prerequisite proves detection of the Library predicate
`Modules.IsFlatOver` for actual module sheaves after flat surjective base change.
The scheme results retain arbitrary universe `u`, arbitrary schemes, and every
module sheaf; quasi-coherence and finiteness are not hypotheses.

For maps `a : P ⟶ X` and `p : P ⟶ T`, the definition `pullbackIsFlatOver a p`
is the object property on `X.Modules` that sends `M` to relative flatness of
its ordinary pullback `a* M` over `T` through `p`. The definition itself needs
no cartesian square or geometric hypothesis.

The algebraic lemma `RelativeFlatnessDescent.flat_of_faithfullyFlat_tensor`
concerns a tower of commutative rings `R → A → B` and an `A`-module `M`.
If `B` is faithfully flat over `A` and `B ⊗[A] M` is flat over `R`, then `M`
is flat over `R`. Its implemented proof uses the tensor injectivity criterion.
For an injection of `R`-modules, the induced tensor map with `M` is `A`-linear.
Faithful flatness detects its injectivity after tensoring with `B`. Tensor
associativity identifies this map with tensoring the original injection with
`B ⊗[A] M`, which is injective by the assumed `R`-flatness. Naturality of
the associativity equivalences is proved on pure tensors.

The lemma `isFlatOver_of_pullback_flat_surjective` descends relative flatness
along a flat surjection `p : X ⟶ Y` of the source, with an arbitrary
`f : Y ⟶ S`. For each `y`, surjectivity supplies `x` above it. The actual
local-ring map from the stalk at `y` to the stalk at `x` is faithfully flat:
it is flat by flatness of `p` and local because it is a scheme stalk map.
The Library's `StalkPullback.pullbackStalkTensorEquiv` identifies the stalk
of `p* M` with extension of scalars of the stalk of `M`. Restricting that
equivalence to the local ring of `S`, the algebraic lemma gives the required
flatness at `y`. The scalar tower uses the actual composite stalk map.

The lemma `isFlatOver_comp_of_flat` proves that composing a structure map
`f : X ⟶ Y` with a flat map `g : Y ⟶ S` preserves relative flatness.
It applies transitivity of module flatness to the actual local-ring actions;
the scalar tower follows from the scheme stalk-map composition identity.

For every cartesian square `H : IsPullback a p f g`, with
`f : X ⟶ S` and a flat surjection `g : T ⟶ S`,
`isFlatOver_iff_pullback_of_flat_surjective` proves
`IsFlatOver f M ↔ IsFlatOver p (a* M)`.
The forward implication is the published arbitrary-base-change preservation
lemma in `RelativeFlatnessPullback`. For the converse, `a` is flat and
surjective by base change. Composition with the flat map `g` gives relative
flatness through `p ≫ g`; the cartesian square identifies this composite with
`a ≫ f`, and source-side descent applies. Finally,
`pullbackIsFlatOver_eq_of_flat_surjective` expresses this equivalence as equality
of object properties.

These are internal consequences of the Library's actual stalk and pullback
constructions and Mathlib's tensor, faithfully flat, and scheme-morphism
results. The imported `FaithfullyFlatPullbackDescent` supplies the faithful
flatness lemma for actual scheme stalk maps. This unit proves relative-flatness
detection only. It does not establish descent of finite presentation,
identify geometric cocycles with module coalgebras, or construct a scheme atlas
for the coherent-family stack.
