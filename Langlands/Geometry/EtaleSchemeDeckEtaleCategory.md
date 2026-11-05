# Etale deck geometry and natural restriction comparisons

This internal construction assembles actual étale deck geometries into a
category. Canonical inverse image and étale restriction give six cohomological
consumer functors on this category, each retaining every base coefficient
sheaf. Three specified natural isomorphisms compare the two constructions.
Six further natural isomorphisms recover ordinary cohomology and sections,
and three full natural-transformation equalities express compatibility of
these recoveries with the comparison.

All new declarations are in
`Langlands.Geometry.EtaleSchemeDeckAction.EtaleDatum`, except the structure
`EtaleDatum` itself in the enclosing namespace.

## Original geometry, variance, and sizes

Fix a scheme `X : Scheme.{u}` and a group `G : Type t`. An `EtaleDatum X G`
extends the existing raw `Datum X G` by requiring its actual projection
`p_A : A.space ⟶ X` to be étale. Its inherited data are an actual scheme,
the original homomorphism `τ_A : G →* (Aut A.space)ᵐᵒᵖ`, and the equations

```
(aut τ_A g).hom ≫ p_A = p_A.
```

The inherited `aut` convention takes the underlying opposite automorphism
back to an automorphism of the original scheme.

An arrow `f : A ⟶ B` extends the raw geometric arrow with étaleness of its
original scheme map. In cohomological variance its data are

```
f.map : B.space ⟶ A.space
f.over_base : f.map ≫ p_A = p_B
f.equivariant g :
  f.map ≫ (aut τ_A g).hom = (aut τ_B g).hom ≫ f.map.
```

Identities use the original identity scheme map, and `f ≫ k` uses
`k.map ≫ f.map`. The projection and arrow étaleness fields give typeclass
instances. Étaleness of identity and composite maps is inherited from the
scheme theory. The over-base and equivariance equations for a composite follow
by associativity and the original equations. The category laws follow from
scheme-map laws using `Hom.ext`; the new étaleness fields are propositions.
The theorems `id_map` and `comp_map` expose these exact scheme maps.

`forget : EtaleDatum X G ⥤ Datum X G` forgets étaleness while preserving all
original geometry. Its functor laws are definitional, and its faithfulness
follows by projecting an equality of raw arrows to their scheme maps and
using `Hom.ext`. `forget_map_map` exposes the preserved map. Composing with
the existing faithful `Datum.overActionFunctor` gives the inherited connection
to actions on the opposite over category. No new full or essentially
surjective assertion is made.

The category and forgetful functor need no coefficient ring or derived
categories. All subsequent constructions fix a commutative ring `R : Type u`
and retain the ambient choices

```
[∀ A : Datum X G, HasDerivedCategory.{wY} (ModuleSheaf A.space R)]
[HasDerivedCategory.{wR} (ModuleCat.{u} R)].
```

This family ranges over all raw data, not just the étale subcategory. It is
the uniform ambient hypothesis inherited from the raw consumers; this unit
does not construct these choices. All six consumers, including sections and
ordinary cohomology, and all their comparisons retain it. There is no
additional separately supplied derived-category instance over `X`. Schemes,
the coefficient ring, and module carriers share universe `u`; the group
universe `t`, common sheaf-derived size `wY`, and module-derived size `wR` are
independent. Degrees of ordinary cohomology and recovery are natural numbers.

## Six functors on geometry and coefficients

For a sheaf `M : ModuleSheaf X R`, write

```
P_A(M) = (inverseImage p_A R).obj M
T_A(M) = (restriction p_A (ModuleCat R)).obj M.
```

These are actual module sheaves on the small étale site of `A.space`.
Write `D_A`, `H_A^n`, and `S_A` for the existing bounded-below derived
global-section, ordinary cohomology, and global-section functors on that
site. The definitions and their underlying values are:

| New functor | Underlying value at `(A,M)` | Construction |
| --- | --- | --- |
| `derivedConsumer R` | `D_A(P_A(M))` | `forget ⋙ Datum.derivedConsumer R` |
| `cohomologyConsumer R n` | `H_A^n(P_A(M))` | `forget ⋙ Datum.cohomologyConsumer R n` |
| `sectionsConsumer R` | `S_A(P_A(M))` | `forget ⋙ Datum.sectionsConsumer R` |
| `restrictionDerivedConsumer R` | `D_A(T_A(M))` | `deckDerivedSectionsFunctor` at `A` |
| `restrictionCohomologyConsumer R n` | `H_A^n(T_A(M))` | `deckCohomologyFunctor` at `A` |
| `restrictionSectionsConsumer R` | `S_A(T_A(M))` | `deckSectionsFunctor` at `A` |

Each is a functor from `EtaleDatum X G` into a category of functors from
`ModuleSheaf X R`. Derived values carry `G`-actions in
`DerivedCategory.Plus (ModuleCat R)`; ordinary and section values carry
`G`-actions in `ModuleCat R`. Thus geometric arrows give entire equivariant
natural transformations in every base sheaf. The six
`*_obj_obj_V` theorems identify the underlying objects in the table.

The canonical functor laws follow by composition with the raw consumers.
The three restriction functors use exactly the previously constructed
`restrictionDerivedMap`, `restrictionCohomologyMap`, and
`restrictionSectionsMap` on original arrows. Their identity and composition
laws are proved, rather than supplied as inputs. The proofs precompose with
the invertible canonical-to-restriction comparison at the source geometry,
apply the parent geometric comparison squares, use the canonical identity
or composition law, and cancel that source isomorphism. For composition the
resulting original map is exactly `k.map ≫ f.map`.

## Exact actions and maps

For a canonical consumer, its `*_obj_obj_ρ` theorem identifies the action
of `g` with actual pullback along `(aut τ_A g).hom`, with coefficient

```
(coefficientIso τ_A p_A A.over_base R g).hom.app M.
```

The three pullback operations are respectively
`sheafDerivedPullbackWithCoefficients`,
`cohomologyPullbackWithCoefficients`, and
`sectionsPullbackWithCoefficients` in `EtaleDerivedGlobalPullback`.
These formulas reuse the specified inverse-image coefficients from the
original geometry.

For restriction consumers, the corresponding action uses the same original
automorphism and the exact restriction coefficient

```
d_A(g,M) =
  (restrictionComp p_A (ModuleCat R) (aut τ_A g).hom).hom.app M ≫
    (restrictionCongr R (A.over_base g)).hom.app M.
```

The derived and ordinary formulas use `derivedSectionsMapWithCoefficients`
and `cohomologyMapWithCoefficients` at this coefficient. The section formula
is geometric `EtalePullback.sectionsMap` at `T_A(M)` followed by
`S_A.map d_A(g,M)`. The proofs expand the inherited action and apply
`restrictionCoefficient_act`. These are constructed group actions, with
their intrinsic laws inherited from the actual equivariant consumers.

For every base sheaf morphism `α : M ⟶ N`, the six
`*_obj_map_hom` theorems identify the underlying morphism as the appropriate
`D_A`, `H_A^n`, or `S_A` applied to `P_A.map α` or `T_A.map α`.
The restriction section case uses `pullbackSectionsFunctor_map_hom`;
the other five formulas are definitional.

For a geometric arrow `f : A ⟶ B`, set

```
b_f(M) =
  (projectionInverseImageIso R p_A p_B f.map f.over_base).hom.app M
c_f(M) =
  (restrictionComp p_A (ModuleCat R) f.map).hom.app M ≫
    (restrictionCongr R f.over_base).hom.app M.
```

The coefficient `b_f(M)` goes from inverse image along `f.map` of `P_A(M)`
to `P_B(M)`. The coefficient `c_f(M)` goes from restriction along `f.map`
of `T_A(M)` to `T_B(M)`. The six `*_map_app_hom` theorems identify:

| Consumer | Underlying geometric morphism at `M` |
| --- | --- |
| Canonical derived | `sheafDerivedPullbackWithCoefficients f.map R b_f(M)` |
| Canonical ordinary | `cohomologyPullbackWithCoefficients f.map R n b_f(M)` |
| Canonical sections | `sectionsPullbackWithCoefficients f.map R b_f(M)` |
| Restriction derived | `derivedSectionsMapWithCoefficients f.map R c_f(M)` |
| Restriction ordinary | `cohomologyMapWithCoefficients f.map R n c_f(M)` |
| Restriction sections | `sectionsMap(f.map)` at `T_A(M)`, then `S_B.map c_f(M)` |

The canonical formulas are definitional. The restriction formulas are the
parent original-arrow formulas applied to precisely `f.map`,
`f.over_base`, and `f.equivariant`. Together the object, action,
coefficient-arrow, and geometric-arrow formulas provide 24 exact component
identifications for the six functors.

## Specified comparisons and recoveries in both inputs

`derivedRestrictionConsumerIso`, `cohomologyRestrictionConsumerIso n`, and
`sectionsRestrictionConsumerIso` compare the respective canonical and
restriction functors. Each is built by `NatIso.ofComponents` from the
specified parent comparison at `A`; its geometric naturality is the parent
`derivedMap_restriction`, `cohomologyMap_restriction`, or
`sectionsMap_restriction` square. Its components are already equivariant
natural isomorphisms in base coefficients, so this assembly preserves
naturality in both inputs.

Write `i_A(M) = (inverseImageIsoRestriction p_A R).hom.app M`.
The three `*RestrictionConsumerIso_hom_app_app_hom` theorems identify the
underlying comparison at `(A,M)` with `D_A.map i_A(M)`,
`H_A^n.map i_A(M)`, and `S_A.map i_A(M)`, respectively. No new choice of
coefficient comparison is made.

Let `W_n` denote postcomposition of a base-coefficient functor with the
action-valued homology functor
`(DerivedCategory.Plus.homologyFunctor (ModuleCat R) n).mapAction G`.
Lean expresses this postcomposition using `Functor.whiskeringRight`.
The recovery isomorphisms are:

```
homologyConsumerIso n :
  derivedConsumer ⋙ W_n ≅ cohomologyConsumer n
derivedZeroConsumerIso :
  derivedConsumer ⋙ W_0 ≅ sectionsConsumer
cohomologyZeroConsumerIso :
  cohomologyConsumer 0 ≅ sectionsConsumer
restrictionHomologyConsumerIso n :
  restrictionDerivedConsumer ⋙ W_n ≅ restrictionCohomologyConsumer n
restrictionDerivedZeroConsumerIso :
  restrictionDerivedConsumer ⋙ W_0 ≅ restrictionSectionsConsumer
restrictionCohomologyZeroConsumerIso :
  restrictionCohomologyConsumer 0 ≅ restrictionSectionsConsumer.
```

All six use `NatIso.ofComponents` with the specified original recovery
isomorphisms. The three canonical geometric naturality proofs are exactly
`derivedMap_homology`, `derivedMap_zero`, and `cohomologyMap_zero`.
The three restriction proofs are exactly `restrictionDerivedMap_homology`,
`restrictionDerivedMap_zero`, and `restrictionCohomologyMap_zero`.
These are full equivariant squares natural in every base coefficient.

The six `*ConsumerIso_hom_app_app_hom` recovery formulas identify the
underlying maps precisely. Canonical homology and derived degree zero use
`homologyNatIso` and `homologyZeroIso` at `P_A(M)`. Canonical ordinary degree
zero is `homologyNatIso` inverse in degree zero followed by `homologyZeroIso`
at `P_A(M)`. Restriction homology and derived degree zero use the same
specified comparisons at `T_A(M)`, after removing the identity component of
the inherited associator. Restriction ordinary degree zero uses the original
`EtaleDerivedSections.cohomologyZeroIso` at `T_A(M)`.

Finally, abbreviate the three canonical-to-restriction comparisons by
`I_D`, `I_H(n)`, `I_S`; canonical recoveries by `h_n`, `z_D`, `z_H`; and
restriction recoveries by `h'_n`, `z'_D`, `z'_H`. The final three theorems
state equalities of entire natural transformations on the geometry category:

```
derivedRestrictionConsumerIso_homology :
  whiskerRight I_D.hom W_n ≫ h'_n.hom = h_n.hom ≫ I_H(n).hom
derivedRestrictionConsumerIso_zero :
  whiskerRight I_D.hom W_0 ≫ z'_D.hom = z_D.hom ≫ I_S.hom
cohomologyRestrictionConsumerIso_zero :
  I_H(0).hom ≫ z'_H.hom = z_H.hom ≫ I_S.hom.
```

The proofs use natural-transformation extensionality at `A` and the parent
fixed-geometry compatibility square. They therefore retain all coefficient
naturality and equivariance already present in that square. The 24 functor
formulas, three comparison formulas, and six recovery formulas give 33 exact
component formulas in total.

## Provenance and remaining scope

This is an internal categorical construction from
`EtaleSchemeDeckCategory`, `EtaleSchemeDeckMapRestriction`,
`EtaleSchemeDeckRestriction`, and `EtaleDeckAction`. The underlying sheaves,
inverse image, restriction, global sections, ordinary right-derived
cohomology, and bounded-below derived sections are the actual existing
constructions on schemes' small étale sites. The new restriction functor
laws use proved geometric comparison squares and invertible cancellation.
The natural isomorphisms reuse the specified component maps and their proved
naturality. No external Harris or Berkovich theorem, desired cohomology
object, or comparison theorem is an additional input.

The group is abstract and the base is fixed. Projections and geometric
arrows in this category are étale; the raw canonical category remains
available for arbitrary scheme maps. This unit supplies neither covering or
torsor properties nor freeness, finiteness, properness, topological
continuity, smoothness, or compact support. It does not construct an
arithmetic level tower, an analytic realization, or a Harris/Shimura
specialization. Those geometric and arithmetic instantiations, including
the required action properties, remain obligations of the broader framework.
