# Scalar restriction of compatible equivariant coefficients

## Scope and provenance

This is an internal construction from the Library's
`EtaleScalarRestriction` and `EtaleEquivariantCoefficientDiagram` modules.
It extends scalar restriction on actual small-etale sheaves with geometric
equivariance to compatible families over a diagram of schemes. It imports
the existing coefficient category, geometric pullback comparisons and
ordinary global-section functors; no external theorem is transcribed.

Let `R` and `A` be commutative rings in universe `u`, with a ring homomorphism
`φ : R →+* A`. The schemes and section-module carriers also have universe
`u`. Let `J` have object universe `v` and morphism universe `w`, and supply
a functor `S : J ⥤ Schemeᵒᵖ`. Every arrow `a : i ⟶ j` is required to give
an etale scheme morphism

```
f_a : (S.obj j).unop ⟶ (S.obj i).unop.
```

Let `G` be a group in universe `t`. Supply actions
`ρ i : G →* (Aut (S.obj i).unop)ᵐᵒᵖ` and their equivariance equations

```
f_a ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ f_a.
```

These are the existing geometric input requirements for
`EquivariantCoefficientDiagram`. The opposite-automorphism convention is
unchanged: the automorphism for `g * h` is that for `g` followed by that for
`h`. No topology is imposed on `G`, and `φ` need not be injective, surjective
or flat.

## Geometric comparison maps

The identity and composition laws of a coefficient diagram use
`diagramRestrictionId` and `diagramRestrictionComp`. These comparisons
include transport along the supplied scheme functor's identity and
composition equations, so preserving the underlying section carriers alone
does not establish the diagram laws.

`scalarRestriction_diagramRestrictionId` proves that applying scalar
restriction to the identity comparison over `A` gives the comparison over
`R` at the restricted sheaf. Likewise,
`scalarRestriction_diagramRestrictionComp` proves the corresponding equality
for every pair of composable diagram arrows. Both proofs evaluate the sheaf
maps on each small-etale object, expand the geometric comparisons, and use
`restrictionCongr_hom_component` for equality transport. Functoriality of
module scalar restriction then identifies the component maps.

## Compatible equivariant coefficients

In namespace `EquivariantCoefficientDiagram`, `restrictScalars φ D`
constructs an `R`-coefficient diagram from an `A`-coefficient diagram `D`.
At vertex `i` it uses `scalarRestrictionFunctor φ (ρ i)`. For an arrow
`a : i ⟶ j`, its transition is the composite of

1. the published `scalarRestrictionPullbackObjIso` from pullback of the
   restricted sheaf to restriction of the pulled-back sheaf;
2. scalar restriction of `D.map a`.

The first map is identity on underlying sheaves and has proved geometric
equivariance. Thus the transition's underlying sheaf map is precisely the
scalar restriction of the original transition, as recorded by
`restrictScalars_map_hom`. On each section module the underlying additive
group and maps are retained, and `r` acts as `φ(r)`.

The diagram's identity law follows from `D.forget.map_id` and the identity
comparison lemma. Its composition law follows by applying sheaf scalar
restriction to `D.forget.map_comp` and using the composition comparison
lemma. Equality is checked on underlying sheaf maps, which suffices for
equivariant morphisms. The new diagram laws are proved, rather than supplied
as assumptions.

`restrictScalarsMap` restricts each component of a compatible coefficient
morphism. Its transition square follows by applying sheaf scalar restriction
to the original square. `restrictScalarsFunctor` packages these constructions
as a functor

```
EquivariantCoefficientDiagram A S ρ hρ
  ⥤ EquivariantCoefficientDiagram R S ρ hρ.
```

Its identity and composition laws hold vertexwise. The functor is faithful
because scalar restriction on each equivariant coefficient category is
faithful and diagram morphisms are determined by their components.
`restrictScalarsEvaluationIso` identifies evaluation after this functor with
evaluation followed by the existing scalar restriction functor; its
components are identities.

## Ordinary section diagrams

Write `Res_φ` for `ModuleCat.restrictScalars φ`. For each `D`,
`restrictScalarsSectionsIso` is a natural isomorphism of `J`-diagrams

```
(restrictScalars φ D).sections
  ≅ D.sections ⋙ Res_φ.mapAction G.
```

At vertex `i` it is the published
`scalarRestrictionSectionsFunctorIso φ (ρ i)` applied to `D.obj i`.
Consequently every component is an isomorphism of `R`-module group actions,
not merely of underlying modules.

Naturality along `a : i ⟶ j` is proved on underlying module maps. The
published formula for section transitions expresses them as geometric
section restriction followed by sections of the coefficient transition.
The ordinary scalar comparison's naturality moves it past `D.map a`;
`scalarRestriction_sectionsMap` moves it past geometric section restriction.
Preservation of composition finishes the square.

`restrictScalarsSectionsFunctorIso` assembles these comparisons naturally
also in `D`. Its target postcomposes the entire section diagram by
`Res_φ.mapAction G`. Naturality in a compatible coefficient morphism is the
published vertexwise equivariant section comparison's naturality.

## Remaining boundaries

These constructions apply to any supplied index category with the stated
geometric data, including inverse diagrams when their arrows are oriented
accordingly. They do not construct an inverse limit or prove a comparison
with such a limit. The section comparison concerns ordinary global sections;
there is no comparison in positive cohomological degree, no preservation of
injectives, and no derived coefficient-change assertion here. This unit
does not construct tensor extension, reduction modulo an ideal, specified
Harris coefficient systems or Shimura towers, smooth or continuous group
actions, analytic sites, or compactly supported cohomology. Coherence under
composition of ring homomorphisms and compatibility with diagram reindexing
remain separate constructions.
