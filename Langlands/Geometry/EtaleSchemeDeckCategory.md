# Raw scheme deck geometry and its cohomological functors

This internal construction makes the original inputs of
`EtaleSchemeDeckAction` into a category and constructs all three consumers
as functors in that geometry and in every base coefficient sheaf. The
cohomological maps, actions, and recovery comparisons are constructed from
the existing actual inverse-image and geometric pullback functors.

## Original geometric category

Fix `X : Scheme.{u}` and `G : Type t` with `[Group G]`.
`EtaleSchemeDeckAction.Datum X G` consists of an actual scheme `space`,
a morphism `projection : space ⟶ X`, a homomorphism
`action : G →* (Aut space)ᵐᵒᵖ`, and the geometric deck equations

```
(aut action g).hom ≫ projection = projection.
```

The inherited `aut` convention satisfies
`aut action (g * h) = aut action g ≪≫ aut action h`.
The datum has no coefficient, cohomology, derived-category, covering, or
topological input.

Arrows follow cohomological variance. An arrow `f : A ⟶ B` has an original
scheme map `f.map : B.space ⟶ A.space` and the equations

```
f.map ≫ A.projection = B.projection
f.map ≫ (aut A.action g).hom = (aut B.action g).hom ≫ f.map.
```

`Datum.Hom` includes these equations as its intrinsic fields. Identity is
the identity scheme map, and the underlying map of `f ≫ k` is
`k.map ≫ f.map`. The over-base and equivariance fields for a composite
follow from associativity and the two input equations. `Hom.ext` reduces
the category laws to the corresponding equalities of actual scheme maps;
`id_map` and `comp_map` expose their exact underlying formulas.

`Datum.overActionFunctor` takes this category to
`Action ((Over X)ᵒᵖ) G`, using the existing `overAction` and `overHom`.
`overActionFunctor_map_left` recovers `f.map` literally. Its proved
`Faithful` instance uses that equality to recover a raw arrow from its
image. This category and functor require no derived-category assumptions.

## Original-map identity and composition

The standalone lemmas `derivedMap_id`, `cohomologyMap_id`, and
`sectionsMap_id` state that each original identity triangle induces the
identity natural transformation, with its complete group action and all
base coefficients.

For original equivariant maps `f : Z ⟶ Y` and `k : W ⟶ Z` over `X`,
`derivedMap_comp`, `cohomologyMap_comp`, and `sectionsMap_comp` state

```
consumerMap f ≫ consumerMap k = consumerMap (k ≫ f).
```

The right side uses the actual composite over-base and equivariance
equations. These are equalities of natural transformations with values in
`Action`, not just equalities of underlying objects or maps on classes.
They impose no etaleness condition on the structure maps or on `f` and `k`.

The derived identity proof combines `derivedMap_app_hom` with
`projectionInverseImageIso_id`. The derived composition proof combines the
actual `sheafDerivedPullbackWithCoefficients_comp` with
`projectionInverseImageIso_comp`, cancelling the inverse-image comparison
and its inverse. The ordinary and section proofs transport these proved
derived laws through the specified invertible recovery maps using the
full `derivedMap_homology` and `derivedMap_zero` squares. They do not infer
equality of derived morphisms from equality after homology.

## Consumers and coefficient scope

Fix a commutative ring `R : Type u`; modules also have universe `u`.
The consumer section retains the ambient choices

```
[∀ A : Datum X G, HasDerivedCategory.{wY} (ModuleSheaf A.space R)]
[HasDerivedCategory.{wR} (ModuleCat.{u} R)].
```

This is a chosen family over all raw data in the source category, with one
common derived-category size `wY`. The size `wR` is independent, as is the
group universe `t`. No instance for sheaves on the base `X` is required.
The standalone map laws need only the original schemes they mention, all
at the common size `wY`, and the module-derived category. All three
consumers, including sections and ordinary cohomology, retain these
choices because their inherited actions and pullback comparisons use the
derived construction. This unit does not construct those ambient
derived-category instances.

`Datum.derivedConsumer R` is a functor

```
Datum X G ⥤
  (ModuleSheaf X R ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G).
```

`Datum.cohomologyConsumer R n`, for `n : ℕ`, and
`Datum.sectionsConsumer R` have the analogous target with `ModuleCat R`.
Their objects are the original `derivedFunctor`, `cohomologyFunctor n`,
and `sectionsFunctor`. Their arrow maps are the original `derivedMap`,
`cohomologyMap n`, and `sectionsMap`; their functor laws are precisely the
proved standalone laws.

The three `*_obj_obj_V` formulas identify evaluation at `A` and `M` with
actual bounded-below derived sections, ordinary degree-`n` cohomology, and
global sections on `A.space` of `(inverseImage A.projection R).obj M`.
These are module sheaves on the original scheme's small etale site.

The `*_obj_obj_ρ` formulas identify every action with geometric pullback
along `(aut A.action g).hom`, with coefficient map

```
(coefficientIso A.action A.projection A.over_base R g).hom.app M.
```

That coefficient comparison is constructed from inverse-image composition
and the original deck equation. The `*_obj_map_hom` formulas identify a
base sheaf morphism `α` with the corresponding sections or cohomology
functor applied to `(inverseImage A.projection R).map α`.

The `*_map_app_hom` formulas identify a raw geometric arrow `f`, evaluated
at `M`, with actual derived, ordinary, or section pullback along `f.map`,
using the coefficient map

```
(projectionInverseImageIso R A.projection B.projection
  f.map f.over_base).hom.app M.
```

Thus both inputs and every deck action retain the supplied original
schemes and their maps.

## Specified recovery natural in both inputs

`Datum.homologyConsumerIso R n` is a natural isomorphism from
`derivedConsumer R` postcomposed by homology on actions, applied pointwise
to the coefficient functors, to `cohomologyConsumer R n`.
`Datum.derivedZeroConsumerIso R` has the corresponding source for homology
in degree zero and target `sectionsConsumer R`.
`Datum.cohomologyZeroConsumerIso R` compares `cohomologyConsumer R 0` with
`sectionsConsumer R`.

Their components at `A` are exactly the parent's `homologyFunctorIso`,
`derivedZeroFunctorIso`, and `cohomologyZeroFunctorIso`. Each is already
natural in coefficients and equivariant for the complete original group.
Their naturality in raw geometric arrows is supplied by the parent's
three full recovery squares, through `NatIso.ofComponents`. The
`*_hom_app_app_hom` formulas further identify their underlying components
at `A` and `M` with the original-scheme `homologyNatIso`,
`homologyZeroIso`, and, for ordinary degree zero, `homologyNatIso` inverse
followed by `homologyZeroIso`, evaluated at the original inverse-image
coefficient. No new arbitrary recovery map is chosen.

## Provenance and remaining scope

This is a derived internal categorical construction from
`EtaleSchemeDeckAction`, `EtaleCanonicalCoefficientDiagram`, and
`EtaleGeometricCoefficientPullback`. Mathlib supplies the ordinary
category, functor-category, action, whiskering, and natural-isomorphism
constructions. No new assertion is attributed to an external source.
The raw datum records genuine geometric input, and all cohomological
outputs and their functor laws are constructed from that input.

The base scheme, coefficient ring, and group are fixed. The actions are
actions of an abstract group; no continuity or smoothness is asserted.
Compact support, freeness, torsor or covering conditions, finiteness,
analytic realization, arithmetic level-tower identifications, and the
Harris and Shimura specializations remain further obligations. This unit
does not compare arbitrary geometric arrows with the older restriction
construction or complete the host Harris framework.
