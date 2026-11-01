# Identity and composition of actual geometric torsor diagrams

This module constructs canonical identity and binary composition comparisons
for geometric base change of actual small-etale objects, cover actions and
whole varying-group cover diagrams. The scheme and group carriers share
universe `u`; index object and morphism universes are independent. Base
morphisms are arbitrary scheme morphisms. No etale hypothesis on the base
morphisms, coefficient modules, finiteness or torsor predicate is needed.

`etaleObjectPullbackId X` identifies identity base change on `X.Etale`
with the identity functor. Its component is the actual first projection
`U ×_X X ⟶ U`, an isomorphism because the other morphism is an identity.
The over-category condition is the fiber-product equation, and naturality
follows from the first-coordinate formula for the pullback map.
`etaleTorsorPullbackId` transports this comparison to actions of a fixed group;
equivariance is supplied by the actual action-functor construction.

For any `D : I ⥤ GrpCat`, `etaleTorsorDiagramPullbackId` transports that
identity comparison to whole diagrams, retaining all group actions, index
transitions and equivariant diagram morphisms. Its forward component at
every index is the original cover's first fiber projection.

For `f : Z ⟶ X` and `g : V ⟶ Z`,
`etaleTorsorDiagramPullbackComp f D g` is a natural isomorphism

```text
pullback along g ; f
  ≅ pullback along f, then pullback along g.
```

The left endpoint uses a single scheme fiber product with the composite base
map. The right endpoint uses actual iterated fiber products, with their
successively pulled-back actions and transitions. The construction applies
`EquivariantDiagram.mapFunctorCongr` to Mathlib's
`MorphismProperty.Over.pullbackComp`, then uses the constructed
`mapFunctorComp` isomorphism. No comparison is supplied as an input.

`etaleTorsorDiagramPullbackComp_hom_fst_fst` proves that the comparison
preserves the original cover coordinate after the two first projections.
`etaleTorsorDiagramPullbackComp_hom_snd` proves that it preserves the final
base coordinate. The first assertion uses Mathlib's actual pullback comparison
formula; the second is the over-category morphism equation. Naturality of
the whole functor comparison includes every original index transition and
every equivariant cover-diagram morphism.

The finite geometric torsor condition, when present, is preserved by each
base-change functor by the previously proved `IsFiniteGeometricTorsor.pullback`.
This module does not assume that condition in order to construct the
comparisons. These are internal categorical constructions from actual scheme
fiber products. Associated coefficient-sheaf comparison coherence, higher
unit/associativity equations, compact supports and actual Shimura realization
are separate obligations.
