# Fixed-scheme equivariant coefficient diagrams

This internal construction specializes the published varying-scheme equivariant
coefficient category to diagrams of equivariant sheaves on one supplied scheme.
It imports `EtaleEquivariantCoefficientDiagram` and
`EtaleCohomologyFixedDiagram`. It transcribes no external theorem.

## Inputs and construction

The input is a scheme `X : Scheme.{u}`, a commutative ring `R : Type u`,
a group `G : Type t`, and an action `ρ : G →* (Aut X)ᵐᵒᵖ` in the published
opposite-automorphism convention: the underlying automorphism of `g * h` is
the automorphism of `g` followed by that of `h`. The diagram category `J` has independent
object and morphism universes `v` and `w`. Given `D : J ⥤ EquivariantSheaf R ρ`,
`ofFixed` uses the constant opposite-scheme diagram `fixedSchemeDiagram X J`,
the constant action family `fun _ => ρ`, and identity-map equivariance.
Every scheme arrow is the identity of `X` and is therefore etale. Here
`EquivariantSheaf R ρ` is the published category of actual small-etale
module sheaves with equivariance for geometric pullback.
Its object at `i` is `D.obj i`; its transition at `a : i ⟶ j` is

```text
(equivariantPullbackId R ρ).hom.app (D.obj i) ≫ D.map a.
```

The identity and composition laws reduce, by underlying equivariant-morphism
extensionality and the published comparison formulas, to the ordinary
`CoefficientDiagram.ofFixed` laws for the underlying sheaf diagram.
`ofFixedMap` uses the original natural-transformation components; its
transition square is the ordinary fixed-scheme square after forgetting.
The construction gives `ofFixedFunctor`, with a faithful instance because
its map on morphisms retains all original components.

`ofFixed_forget` is the equality with the ordinary fixed-scheme construction.
`ofFixedForgetFunctorIso` and `ofFixedEvaluationIso` package forgetting and
evaluation compatibilities as reflexive functor isomorphisms, using definitional
equality of component data and proof irrelevance of law fields.

## Cohomology and sections

`ofFixed_cohomology_map` identifies the induced transition with
`(pullbackCohomologyFunctor R ρ q).map (D.map a)`. Its proof uses action-morphism
extensionality and the published ordinary fixed-scheme cohomology formula.
`ofFixed_sections_map` identifies the analogous transition with
`(pullbackSectionsFunctor R ρ).map (D.map a)`. Its proof first uses
`Action.Hom.ext`, `sections_map_hom`, and the published ordinary
`CoefficientDiagram.sections_map` formula. The resulting underlying map is

```text
sectionsMap (𝟙 X) R at (D.obj i).obj
  ≫ sections(X,R).map
      (restrictionId at (D.obj i).obj ≫ (D.map a).hom).
```

Functoriality and associativity isolate the identity geometric restriction
and its identity comparison. `EtalePullback.sectionsMap_id` identifies their
composite with the identity, leaving the section map of the original coefficient
morphism. This proof has a finite local heartbeat limit of `600000`.

`ofFixedCohomologyIso` and `ofFixedSectionsIso` have identity components in
`Action (ModuleCat R) G` and identify the varying-scheme functors with
postcomposition of `D` by the respective fixed-scheme functor. Their functor-level
versions are natural in the full coefficient diagram. The two
`ofFixed_cohomologyZeroIso_*_app` formulas identify both directions of the
canonical degree-zero comparison with its original vertexwise counterpart.
The naturality proofs for the objectwise comparisons use the two map formulas
above. The functor-level comparisons are natural because coefficient morphisms
have the same components on both sides; their component equations reduce to
composition with identities. The degree-zero component formulas are definitional
equalities. No additional comparison theorem is assumed.

## Scope and provenance

The geometry, group action, ring and diagram of actual small-etale equivariant
module sheaves remain supplied inputs. No topology or smoothness is asserted,
and no analytic site, compact supports, trace or actual Harris specialization
is constructed. Ordinary small-etale cohomology is the existing right-derived
section functor. The internal provenance is the identity pullback construction
and the actual component formulas of the imported categories and functors.
In particular, the ordinary fixed-scheme laws come from
`EtaleCohomologyFixedDiagram`, the equivariant identity comparison from
`EtaleEquivariantPullbackFunctoriality`, and the action-valued functors from
`EtaleEquivariantCoefficientDiagram` and `EtaleActionFunctor`. The construction
provides a fixed-scheme coefficient-diagram interface inside the broader geometric
framework; it does not construct the geometric or analytic specialization of Harris.
