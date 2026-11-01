# Coherence of actual geometric torsor base change

This module constructs equality transport and proves the two unit laws and the
associativity law for actual scheme fiber-product base change on small-etale
objects and on complete varying-group cover diagrams. Schemes and group
carriers share universe `u`. The index category has independent object and
morphism universes `uI`, `vI`. All base morphisms are arbitrary scheme morphisms.
No coefficient ring, etaleness of the base maps, finiteness or torsor predicate
is required for these constructions.

For `f : Z ⟶ X`, write `P(f)` for `etaleObjectPullback f`. Its value at a
small-etale object `U` is the actual scheme fiber product `U ×_X Z`, with second
projection to `Z`. `etaleObjectPullbackCongr e` transports this construction
along an equality `e : f = k`, using Mathlib's `Over.pullbackCongr`.
`etaleObjectPullbackComp f g` is Mathlib's `Over.pullbackComp g f`, with orientation

```text
P(g ≫ f) ≅ P(f) ⋙ P(g).
```

The congruence component preserves both fiber projections. The composition
component preserves the original-cover coordinate after the two first
projections, and preserves the final-base coordinate after the second
projection. Its intermediate-base coordinate is the direct new-base projection
followed by `g`. The map formulas identify geometric pullback of an over-category
morphism by its first projection and unchanged new-base projection.

The two object unit laws compare actual morphisms in `Z.Etale`, including the
necessary equality transport of the base map:

- `etaleObjectPullbackComp_id_target` says that composition comparison for
  `P(f ≫ 𝟙 X)`, followed by `P(f)` applied to the first-projection identity
  comparison on `X`, equals congruence for `f ≫ 𝟙 X = f`.
- `etaleObjectPullbackComp_id_source` says that composition comparison for
  `P(𝟙 Z ≫ f)`, followed by the first-projection identity comparison on `Z`,
  equals congruence for `𝟙 Z ≫ f = f`.

For `f : Z ⟶ X`, `g : V ⟶ Z`, `h : W ⟶ V`, and `U : X.Etale`,
`etaleObjectPullbackComp_assoc` compares the following two routes from
`P((h ≫ g) ≫ f)(U)` to `P(h)(P(g)(P(f)(U)))`:

```text
C(f, h ≫ g) at U ; C(g, h) at P(f)(U)
  =
Q(assoc h g f) at U ; C(g ≫ f, h) at U ; P(h)(C(f, g) at U).
```

Here `C` is the forward composition comparison and `Q` is forward equality
transport. Thus the theorem accounts for the associativity of the base maps,
instead of identifying differently parenthesized composites by an assumption.
The unit proofs use over-category extensionality and the two fiber projections.
The associativity proof exposes six underlying scheme maps, records their
projection equations, and applies the fiber-product universal property three
times. Each resulting coordinate equation follows from those projection
identities and the pullback-square equation, with reassociation where needed.

For any `D : I ⥤ GrpCat`, `etaleTorsorDiagramPullbackCongr D e` transports the
same equality comparison through `EquivariantDiagram.mapFunctorCongr`. Its
components at every index are exactly the object comparisons. Component lemmas
also identify the previously constructed diagram identity and composition maps
with their object counterparts. Consequently
`etaleTorsorDiagramPullbackComp_id_target`,
`etaleTorsorDiagramPullbackComp_id_source` and
`etaleTorsorDiagramPullbackComp_assoc` prove the same equations as equalities of
complete equivariant diagram morphisms. These retain every deck action and
index transition. Their proofs apply extensionality for equivariant diagram
morphisms and natural transformations and then the proved object equations.

This is internal categorical infrastructure derived from actual scheme fiber
products, Mathlib's morphism-property over-category comparisons and the existing
functor on equivariant diagrams. No desired comparison or coherence equation is
supplied as input. The existing preservation theorem for finite geometric
torsors continues to apply when that additional predicate is supplied. Coherence
of associated coefficient-sheaf comparisons, arbitrary non-etale sheaf inverse
image, algebraic-closure base change, compact supports and realization by
particular Shimura towers remain separate obligations.
