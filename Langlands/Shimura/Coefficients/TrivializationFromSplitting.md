# Associated-sheaf trivialization from splitting of graph restrictions

Author: Worker 149. This is a derived categorical construction with explicit
hypotheses, not a proof of `EtaleAssociatedTrivializationStatement`.

## Interface and scope

Let `C : Type w` have `Category.{v} C` and binary products, let `J` be a
Grothendieck topology on `C`, and let `Y : Action C G`, where `G : Type u`
is a group. Let `R : Type u` be a commutative ring. No finiteness or geometric
hypothesis is used in this module.

For `U : Over Y.V`, the graph indexed by `g : G` is the morphism
`prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left) : U.left ⟶ Y.V × U.left`.
`graphRestriction` is restriction of an arbitrary module sheaf along that
graph. The hypothesis of `associatedTrivializationOfSplitting` is that,
for every `R`-module sheaf `F` and every such `U`, the map from sections of
`F` on `Y.V × U.left` to functions `G → F(U.left)` given by these
restrictions is bijective.

Under precisely that hypothesis, `associatedTrivializationOfSplitting`
constructs a natural isomorphism between `associatedFunctor J Y` followed
by `J.overPullback (ModuleCat R) Y.V` and the forgetful functor from actions
on module sheaves followed by that same restriction. It is natural in every
equivariant morphism of coefficient sheaves.

When `HasSheafify J (ModuleCat R)` is available,
`constantAssociatedTrivializationOfSplitting` specializes this isomorphism
to module representations via the action functor of `constantSheaf`.
Its right side is the base constant sheaf restricted by `overPullback`.
It makes no identification with an independently constructed constant
sheaf on the slice site.

## Implemented construction and proof

`productEvaluation` restricts a section on `Y × U` along the graph of
`U.hom`, and `associatedEvaluation` first applies the published invariant
inclusion. Their naturality gives `associatedEvaluationNat`.

The invariant inclusion is injective on sections, and every invariant
section is in its image. The proofs map its defining limit over
`SingleObj G` through the sheaf inclusion, evaluation at an object, and the
forgetful functor to types. These functors preserve that limit; Mathlib's
equivalence between a type-valued limit and compatible families supplies
injectivity and the invariant-section lift.

`graphRestriction_diagonal` identifies restriction of the diagonal action
by `g` to the graph indexed by `h` with restriction to the graph indexed by
`g⁻¹ * h`, followed by the coefficient action of `g`. Consequently, for an
invariant section, its value on the graph of `g` is the coefficient action
of `g` applied to its value on the identity graph.

For injectivity of evaluation, equal values on the identity graph therefore
give equal values on all graphs. Injectivity of the assumed graph
restriction map gives equal sections over the cover, and injectivity of
the invariant inclusion gives equal associated sections.

For surjectivity, a section `x` of the underlying coefficient sheaf
specifies the family whose value at `g` is the coefficient action of `g`
on `x`. Surjectivity of graph restriction produces a section `s` over the
cover. The graph-diagonal identity and the group-action law show that every
diagonal translate of `s` has the same restrictions as `s`; injectivity
of graph restriction proves invariance. The limit property then lifts `s`
to the associated sheaf, and its identity-graph value is `x`.

Bijective module homomorphisms are isomorphisms. Componentwise isomorphism
criteria for natural transformations and for the full subcategory of
sheaves upgrade this pointwise proof to the stated natural isomorphism.
The constant-coefficient construction is the specialization along
`(constantSheaf J (ModuleCat R)).mapAction G`.

## Provenance and boundary

This module is derived from the published invariant construction in
`Coefficients.Associated` and Mathlib's categorical limit and isomorphism
APIs. It is an internal reduction of the existing geometric local
trivialization target, not an additional assertion attributed to a source.
No existing Library declaration or its paired Markdown is changed.

The hypothesis on graph restrictions is substantial and is not proved here.
In particular, this module does not assert that `IsFiniteGeometricTorsor`
implies that hypothesis. The separate geometric prerequisite must establish
that implication before this construction proves the original target.
There are no new axioms or proof holes.
