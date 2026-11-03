# Self-centralizing tori are geometrically maximal

This derived unit proves a maximality criterion for the actual torus inclusion
`j : T.toGrp ⟶ G` over any field `k`, and applies it after every field extension.
It uses the published all-test centralizer, represented-subgroup factorization,
and base-change comparisons. Worker 1379 suggested the criterion and its
base-change proof route; Worker 146 implements it here.

## Actual comparison isomorphism

`selfCentralizingComparisonIso` works over any base scheme `S`. Let `T` and
`T'` be commutative group schemes with closed inclusions `j` and `j'` into
`G`, and let `f : T.toGrp ⟶ T'.toGrp` satisfy `f ≫ j' = j`. If
`torusCentralizer j = SubgroupFunctor.range j`, it constructs an actual
isomorphism `T.toGrp ≅ T'.toGrp` whose forward morphism is the supplied `f`.
The lemmas `selfCentralizingComparisonIso_hom` and
`selfCentralizingComparisonIso_hom_comp` record the forward map and its
compatibility with the ambient inclusions. This construction needs no torus or
field hypothesis.

The image of the commutative group `T'` centralizes itself. Restricting its
points along `f` shows that its image centralizes `j`. The assumed equality
therefore puts `range j'` inside `range j`. The closed inclusion `j`
represents its own range, so the published `IsRepresentedBy.factorHom`
constructs `g : T'.toGrp ⟶ T.toGrp` with `g ≫ j = j'`. The identities
`f ≫ g = 𝟙 _` and `g ≫ f = 𝟙 _` follow by cancelling the two representing
inclusions. The construction uses `f` and `g` as its two morphisms.

## Criterion

`isMaximalTorus_of_torusCentralizer_eq` assumes that `T` is a torus, `j` is a
closed subgroup inclusion, and

`torusCentralizer j = SubgroupFunctor.range j`.

It proves `IsMaximalTorus j`. The centralizer equality is equality of subgroup
functors on every test scheme, including after restriction to every further
test scheme. The conclusion uses the published maximality definition: every
factorization `f ≫ j' = j` through a closed torus inclusion `j'` has `IsIso f`.
No smoothness, affineness, connectedness, reductivity or splitness assumption
on the ambient group is needed.

Every comparison in the maximality definition is the forward map of
`selfCentralizingComparisonIso`, and hence is an isomorphism.

## Field extension

`isMaximalTorus_baseChange_of_torusCentralizer_eq` has the same three
hypotheses over `k`. For every field `K` in the same universe with an
`Algebra k K` structure, it proves maximality of the actual pullback inclusion
`T_K.toGrp ⟶ G_K`.

The published `IsTorus.baseChange` and `IsClosedSubgroup.baseChange` preserve
the first two hypotheses. The published `torusCentralizer_baseChange` and
`SubgroupFunctor.range_baseChangeHom` carry the assumed centralizer equality
to the pullback. Applying the criterion over `K` proves the conclusion.
The extension need not be algebraic, finite or separable.

## Scope

This criterion does not prove that a maximal torus is self-centralizing in a
connected reductive group, and does not prove general preservation of maximal
tori under field extension. A proof of the required self-centralizer equality
would make this criterion available for the specified split maximal torus in
`SplitParabolicCocharacterStatement`; that equality and the remaining
geometric parabolic classification remain separate obligations. No unproved
classification proposition is used in either proof.
