# Balanced cube factors and elementary comparison maps

This internal construction supplies the two tensors in the balanced cube formula
and explicit isomorphisms for reindexing and insertion of a constant identity map.
It does not prove the geometric or balanced cube theorem.

Work over any base scheme `S`, with `G : Grp (Over S)`, an arbitrary object
`T : Over S`, three maps `f g h : T ⟶ G.X`, and an actual line bundle `L` on
`G.X.left`. The abbreviation `pull G L a` is precisely the underlying scheme-module
pullback `a.left` applied to `L.obj`. In `Langlands.GroupScheme.BalancedCube`, the
objects are

- `positive G L f g h`: `Q(f*g*h) ⊗ (Q(f) ⊗ (Q(g) ⊗ Q(h)))`;
- `negative G L f g h`: `Q(f*g) ⊗ (Q(f*h) ⊗ Q(g*h))`.

Every displayed tensor is `Langlands.Scheme.Modules.tensorObj`, the existing
sheafified tensor. The word `negative` identifies the pair-indexed side of the
balanced formula; the definition takes no inverse. Multiplication is Mathlib's
pointwise group law on maps into the group object, not composition. Commutativity,
smoothness, properness, connectedness and a field base are unnecessary for these
constructions.

`positiveLineBundle` and `negativeLineBundle` package these actual module sheaves
as line bundles. They take the explicit hypothesis
`pullbackTensorComparisonIsIsoStatement.{u}` and apply the published local-rank-one
pullback and tensor-closure lemmas. They do not install an unproved global instance.

The three `firstUnitIso`, `secondUnitIso`, and `thirdUnitIso` constructions require
an actual isomorphism `Q(1) ≅ structureSheaf T.left`. They compare the positive and
negative objects when respectively `f`, `g`, or `h` is the constant identity map.
After simplifying the group identities, the first removes a unit and rotates three
factors using the tensor commutor and associator. The second removes a unit and
swaps the first two factors using the associator and commutor. The third removes
a final right unit. All remaining factors are transported with the existing
tensor bifunctor's `mapIso`. These maps do not assert that a constant-factor
trivialization always exists over an arbitrary base.

`pullPullIso` is the existing composition comparison for scheme-module pullback
applied to `L.obj`. With the same explicit tensor-comparison invertibility
hypothesis, `pullPositiveIso` and `pullNegativeIso` distribute pullback across
the nested tensors, apply `pullPullIso` to each factor, and use
`MonObj.comp_mul` to identify precomposition of pointwise products. For any
`k : U ⟶ T` the resulting factors are exactly those for `k ≫ f`, `k ≫ g`, and
`k ≫ h`, in the original order and association. Neither domain has any geometric
restriction.

## Provenance and remaining obligations

These are internal categorical constructions from the published pullback,
tensor, associator, commutor, and unitors. Their design matches the balancing of
Milne's *Abelian Varieties*, Corollary 6.4 and the pullback argument in Corollary
6.5, printed/PDF p.9, author corrected January 2, 2022 version of the 1986 chapter.
The original supplies the geometric motivation; it does not state these Lean
helper interfaces. The retained source is registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`, at
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
The rendered p.9 has an omitted inverse on `(f+h)^*L` in Corollary 6.5; the balanced
factor choice follows the three inverse pair factors of Corollary 6.4.

A later proof must establish the tensor-comparison hypothesis, trivialize the
identity fibre over a field, connect the coordinate maps with the published
`CubeFace` maps, and invoke a proved geometric cube result. No global isomorphism
for three arbitrary maps, field triviality result, or geometric cube result is
asserted here. The final balanced cube theorem must discharge every helper
hypothesis and retain its exact unconditional Library target.
