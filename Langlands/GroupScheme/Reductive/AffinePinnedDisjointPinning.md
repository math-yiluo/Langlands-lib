# Pinning preservation on disjoint components

Let `q i : Z i ⟶ T` be any small disjoint scheme decomposition, expressed by
`IsIso (Sigma.desc q)`. For affine pinned models `M`, `N` and base maps `f`,
`g` out of `T`, `Disjoint.comparison q d` assembles any family
`d i : Comparison (q i ≫ f) (q i ≫ g)` into an actual
`Comparison f g`. The theorem `pullComparison_comparison` states that its
normalized direct pullback along each `q i` recovers exactly `d i`.
`comparison_isLocallyPinned` proves that the assembled comparison preserves
the specified coordinate tori, canonical ambient cocharacters and original
pinning vectors on all local affine tests whenever each component does.
There is no finiteness, connectedness or nonemptiness hypothesis on the
indexing type, components or base.

This is an internal application of the existing disjoint-component
group-scheme assembly and normalized pinned-model pullback interfaces:

1. `rootVectorPoint_of_pullComparison` reflects an individual pinning-vector
   equation from a refined test to its original test. It projects through
   `baseChangeCompIso` and the first pullback projection. Naturality of
   the pulled-back comparison and `rootVectorPoint_pull` identify both
   projected points with the original pinning-vector points.
2. `PreservesLocalPinning.of_openCover` proves the pinning-vector clause
   locally for any jointly surjective family of open immersions. For a
   test `Spec A ⟶ T` with `A` local, choose a chart containing the image of
   its closed point. Every point of `Spec A` specializes to the closed
   point, so the entire test has image in that open chart. Lift the test
   through the open immersion, use the chart's pinning equivalence, then
   apply the preceding reflection lemma. The chosen equivalence may
   depend on the local affine test, as the definition requires.
3. `Disjoint.comparison` converts each direct component comparison to its
   iterated pullback endpoints with `comparisonToIterated` and assembles
   these by `Descent.DisjointComponents.groupIso`. Its restriction
   identity follows from `map_groupIso` and cancellation of the actual
   endpoint identifications.
4. `preservesTorus_of_components` assembles the component torus
   isomorphisms after conjugating by the normalized split-torus
   base-change identifications. Component restriction detects equality
   of the resulting inclusion square.
   `preservesCocharacter_of_components` detects the exact cocharacter
   equality in the same way, using `cocharacterOver_pull` and normalized
   cocharacter base change.
5. `isLocallyPinned_of_components` combines these geometric assertions
   with pinning locality from step 2, since all component maps are open
   immersions and jointly cover `T`. Applying the restriction identity
   gives `comparison_isLocallyPinned`.

The construction requires the two models, all component comparisons and a
specified disjoint decomposition. It asserts no existence of pinned
corrections for a supplied arbitrary comparison and does not by itself
prove the parent comparison-existence statement.
