# Canonical coefficients and cohomology of actual over-base deck towers

This module constructs canonical coefficient diagrams and their cohomological
consumers from actual schemes over one base, actual group actions and actual
contravariant level maps. All coefficients arise by inverse image from the
original base. The namespace is
`Langlands.Geometry.EtaleCanonicalDeckTower`.

## Inputs and conventions

Let `X : Scheme.{u}`, let `J : Type v` have `Category.{w} J`, and let
`G : Type t` be a group. The geometric input is an actual functor

```lean
A : J ⥤ Action ((Over X)ᵒᵖ) G
```

For a level `i`, write `Yᵢ := (A.obj i).V.unop.left` and
`pᵢ := (A.obj i).V.unop.hom : Yᵢ ⟶ X`. A group element gives the
scheme map `dᵢ(g) := ((A.obj i).ρ g).unop.left : Yᵢ ⟶ Yᵢ`. A level
arrow `a : i ⟶ j` gives
`fₐ := (A.map a).hom.unop.left : Yⱼ ⟶ Yᵢ`. Their over-category
morphism fields prove `dᵢ(g) ≫ pᵢ = pᵢ` and `fₐ ≫ pᵢ = pⱼ`.
The action is expressed in the opposite category, so its underlying scheme
maps have the corresponding contravariant multiplication convention.
Equivariance of level maps and the action and functor laws are intrinsic to
these existing mathematical objects.

The coefficient ring is any `R : Type u` with `CommRing R`.
`ModuleSheaf X R` is the existing category of `ModuleCat.{u} R`-valued
sheaves on the actual small etale site of `X`. Every such sheaf and every
morphism is allowed. Schemes, the coefficient ring and coefficient modules
share universe `u`; the level object, level morphism and group universes are
independent.

The geometric input supplies no coefficient cocycle, cohomology object,
cohomological action or pullback compatibility. No etaleness, finiteness,
properness, freeness, transitivity or covering hypothesis is imposed on the
geometric maps. The word "deck" here designates over-base automorphisms; the
module does not assert that the input is a Galois covering or a torsor.
There is no topology on `G` in this construction.

## The original geometry and projection

`overDiagram` uncurries the original action diagram using
`Action.functorCategoryEquivalence`, obtaining a functor from
`J × SingleObj G` to `(Over X)ᵒᵖ`. `schemeDiagram` composes this with
`(Over.forget X).op`. `projection` is the natural transformation

```lean
(Functor.const (J × SingleObj G)).obj (Opposite.op X) ⟶ schemeDiagram A
```

whose unop component is the original structure map `pᵢ`. Its naturality
proof is exactly `Over.w`, after unop and removal of the identity map.

The object and projection formulas are reflexive equalities. For a product
arrow `a : (i, *) ⟶ (j, *)`, `schemeDiagram_map` identifies its unop with
`dⱼ(a.2) ≫ f_(a.1)`. The pure-group and pure-level formulas simplify the
original functor's identity and the action's unit law, recovering exactly
`dᵢ(g)` and `fₐ`. `groupMap_isIso` obtains invertibility of `dᵢ(g)` from
`ρAut`, unop and the over-category forgetful functor. Level maps have no
invertibility requirement.

`groupCoefficientIso` and `levelCoefficientIso` evaluate the existing
`projectionInverseImageIso` on the literal `Over.w` triangles. In particular,
for an original base sheaf `M`, the two comparisons have the respective forms

```text
dᵢ(g)* (pᵢ* M) ≅ pᵢ* M,
fₐ* (pᵢ* M)    ≅ pⱼ* M.
```

Here `f*` denotes the constructed inverse-image functor. Each comparison is
inverse-image composition followed by transport along the stated triangle.
It is an isomorphism of coefficient sheaves even when the level scheme map
is not invertible.

## Canonical coefficients and every base morphism

`coefficientFunctor R A` is
`canonicalCoefficientsFunctor R (projection A)`, with target
`CoefficientDiagram R (schemeDiagram A)`. Its vertex at `(i, *)` is exactly
`pᵢ* M`. Its transition on a product arrow is the actual
`projectionInverseImageIso` evaluated at `M`, with the triangle supplied by
naturality of `projection`. For every base-sheaf morphism `α : M ⟶ N`, the
vertex component is exactly `pᵢ*(α)`.

The displayed object, transition and morphism formulas are proved by
reflexivity. All identity, composition and coefficient-naturality fields
come from the existing canonical coefficient construction, which proves
triangle coherence from the actual inverse-image functors. No family of
chosen transition maps is an additional input here.

## Derived, ordinary and section consumers

The `Cohomology` section assumes, at every product vertex, the existing
`HasDerivedCategory.{wS}` for the corresponding `ModuleSheaf` category, and
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`. The two derived-category
universes are explicit and independent. These are ambient category
existence instances, rather than supplied cohomology groups or actions.
The section carries these assumptions also for its ordinary and section
consumers.

The three functors compose `coefficientFunctor` with the existing actual
geometric action consumers:

| Declaration | Underlying object at `M, i` |
| --- | --- |
| `derivedFunctor` | `EtaleDerivedSectionsPlus.derivedSections Yᵢ R` evaluated at `pᵢ* M` |
| `cohomologyFunctor q`, `q : ℕ` | `EtaleDerivedSections.cohomology Yᵢ R q` evaluated at `pᵢ* M` |
| `sectionsFunctor` | `EtaleDerivedSections.sections Yᵢ R` evaluated at `pᵢ* M` |

Their targets are `J`-diagrams of `G`-actions, in respectively the existing
bounded-below derived category and `ModuleCat.{u} R`. In all three cases,
the group action is precisely the existing pullback-with-coefficients map
along `dᵢ(g)`, using `groupCoefficientIso`; the level arrow is precisely
pullback along `fₐ`, using `levelCoefficientIso`. The six original-map
formulas are proved in the module, not stipulated as extra compatibility.
For each proof, equality of the product-index scheme arrow with the original
arrow is lifted to the subtype of arrows satisfying the fixed projection
triangle. Congruence of pullback-with-coefficients on this subtype proves
the formula, including its dependent coefficient comparison.

A base-sheaf morphism acts by the corresponding actual derived-section,
cohomology or section functor applied to `pᵢ*(α)`. Each of these three
formulas is reflexive. Thus naturality includes every original base
coefficient morphism, as well as group equivariance and level compatibility.
These are abstract group actions; no smoothness or continuity is claimed.

## Homology and degree zero

`homologyFunctorIso q` identifies pointwise derived homology of
`derivedFunctor` with `cohomologyFunctor q` as functors in the original base
sheaf. `derivedZeroFunctorIso` identifies degree-zero derived homology with
`sectionsFunctor`, and `cohomologyZeroFunctorIso` identifies ordinary
cohomology in degree zero with `sectionsFunctor`.

Each is obtained by left whiskering the corresponding existing
`CoefficientDiagram` natural isomorphism. Hence each is natural in every
base sheaf and morphism, equivariant for `G`, and compatible with all level
maps. The three component lemmas identify their underlying maps with the
original `homologyNatIso` and `homologyZeroIso` at `Yᵢ` and `pᵢ* M`.
The ordinary degree-zero component is the inverse homology comparison
followed by the canonical zero-to-sections comparison. These component
formulas hold by reflexivity.

## Reindexing the geometry and coefficients

For another arbitrary category `K : Type v'` with `Category.{w'} K`, a group
`H : Type t'`, a functor `F : K ⥤ J` and a homomorphism `φ : H →* G`,
`reindex A F φ` selects the original levels and restricts their original
over-base actions by the existing `actionDiagramReindexFunctor`.

`schemeDiagram_reindex` and `projection_reindex` prove by reflexivity that
the resulting schemes and projections are the original ones reindexed by
`F.prod (SingleObj.mapHom H G φ)`. `reindexCoefficientFunctorIso` compares
canonical coefficients of this geometry with reindexing the original
canonical coefficients. It is the inverse of the existing canonical
coefficient reindexing isomorphism, so it is natural in every base sheaf
and morphism; both component directions are the identity sheaf map.
This module constructs these geometric and coefficient comparisons. A
specialized reindexing comparison for its three cohomological functors
remains a separate implementation obligation; the generic comparison API
is already available in `EtaleGeometricActionReindex`.

## Provenance and retained scope

This is an internal categorical specialization of the existing `Over`,
`Action`, inverse-image coefficient and geometric cohomology constructions.
It asserts no new fact attributed to external literature. The triangle
coherence is reused from `EtaleCanonicalCoefficientDiagram`; the action,
level and coefficient-morphism laws and homology comparisons are reused
from the geometric coefficient action API imported through
`EtaleGeometricActionReindex`. The original geometry formulas and
subtype-congruence arguments identify these constructions with the raw
scheme arrows of the input. Worker 13 implemented this specialization;
the imported canonical coefficient construction separately credits
Worker 57's generalized proof pattern.

The input is actual geometric data but is not yet an instantiated Harris or
Shimura tower. Smooth or continuous group actions, analytic-etale
realizations, compact-support and trace comparisons, arithmetic Hecke and
Galois identifications, and Harris compatibility remain separate obligations.
This contribution advances the definition framework and does not complete
the broader Harris task.
