# Cohomological diagram comparisons under coefficient transport

This internal construction compares the existing actual geometric and
restriction cohomological diagrams after transporting restriction coefficients
to geometric coefficients. It constructs comparison isomorphisms for
bounded-below derived sections, ordinary cohomology in every nonnegative degree,
and actual global sections. Each comparison is natural both in the scheme
diagram arrows and in compatible coefficient morphisms.

## Inputs and scope

Let `J : Type v` have `Category.{w} J`, let
`S : J ⥤ Scheme.{u}ᵒᵖ`, and write `X_i = (S.obj i).unop`.
Every scheme transition `f_a = (S.map a).unop : X_j ⟶ X_i` is assumed
etale. The coefficient ring `R : Type u` is any commutative ring and module
carriers lie in universe `u`. Transition morphisms of coefficient sheaves
need not be invertible; there is no field, finiteness, Noetherian or
local-constancy condition.

The geometric diagram implementation uses
`HasDerivedCategory.{wS} (ModuleSheaf X_i R)` for all vertices, with a common
universe `wS`. It also uses the independent instance
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`. These localization hypotheses
are retained in all six declarations here, including ordinary cohomology and
sections, because their geometric diagram arrows are defined by homology
transport from derived sections.

Let `D` be an actual restriction coefficient diagram, as defined in
`EtaleCohomologyDiagram`. The preceding module
`EtaleCoefficientEquivalence` constructs `ofRestriction D`, whose sheaves are
exactly `D.obj i` and whose coefficient transition along `a` is

```text
(inverseImageIsoRestriction f_a R).hom.app (D.obj i) ≫ D.map a.
```

The sheaf-level diagram laws of this transport were proved in that module.
No cohomological object, transition or desired comparison is supplied as
additional input here.

## Derived-section comparison

`ofRestrictionDerivedSectionsIso D` has type

```text
(ofRestriction D).derivedSections ≅ D.derivedSections.
```

The source uses the geometric diagram construction from
`EtaleGeometricCoefficientDiagram`; the target is the restriction construction
from `EtaleDerivedDiagram`. Their vertex objects are the same actual derived
sections of `D.obj i`, with the sheaf embedded in degree zero. Every component
of the isomorphism is the identity on that object.

To prove naturality along an arrow `a`, the implementation expands the
transported coefficient transition and applies
`sheafDerivedPullbackWithCoefficients_restriction`. That existing theorem
identifies geometric pullback followed by the transported coefficient map
with the actual restriction-based derived map. The identity factors then
cancel. Thus the comparison identifies the actual diagram arrows.

`ofRestrictionDerivedSectionsFunctorIso` packages these isomorphisms into
a natural isomorphism

```text
ofRestrictionFunctor ⋙ geometricDerivedSectionsFunctor
  ≅ restrictionDerivedSectionsFunctor.
```

Here the longer names distinguish the geometric and restriction namespaces;
in Lean each latter functor is named `derivedSectionsFunctor` in its
coefficient-diagram namespace. Both constructions send a compatible
coefficient morphism `alpha` at vertex `i` to actual derived sections applied
to `alpha.app i`. Since coefficient transport preserves that component
morphism, naturality in coefficients reduces to the identity laws.

## Ordinary-cohomology comparison

For `q : Nat`, `ofRestrictionCohomologyIso D q` identifies
`(ofRestriction D).cohomology q` with `D.cohomology q`. Its components are
identities on the actual ordinary right-derived cohomology modules.
The geometric diagram's existing `cohomology_map` theorem identifies its
transported arrow with `cohomologyPullbackWithCoefficients`. Applying
`cohomologyPullbackWithCoefficients_restriction` then gives exactly the
restriction diagram arrow.

`ofRestrictionCohomologyFunctorIso q` proves this identification is natural
in the compatible coefficients as well. On either side, the component map
of a coefficient morphism is the ordinary cohomology functor applied to
the same `alpha.app i`, so again the naturality equation reduces to
identity laws.

## Global-section comparison

`ofRestrictionSectionsIso D` identifies
`(ofRestriction D).sections` with `D.sections`, with identity components on
the actual section modules. The source diagram was transported from derived
degree-zero homology; the target was transported from ordinary degree-zero
cohomology. The two existing `sections_map` theorems identify their arrows
with actual geometric and restriction section pullback followed by the
coefficient maps. Expanding the geometric coefficient composite and using
`sectionsPullback_restriction` proves equality of these arrows.

`ofRestrictionSectionsFunctorIso` proves naturality in coefficients.
The geometric section functor applies ordinary sections to `alpha.app i`;
the restriction functor's `sectionsFunctor_map_app` theorem proves the same
formula for its transported coefficient map. These formulas and the identity
laws prove the naturality equation.

## Provenance and remaining obligations

This is internal categorical assembly of actual previously constructed
functors. The identity components are justified by the proved geometric
pullback/restriction equalities and the preceding coefficient transport.
The module introduces no external mathematical assertion from Harris or
Berkovich.

This group gives the comparison after transporting restriction coefficients
to geometric coefficients. Explicit comparisons in the reverse transport
direction, and equations expressing compatibility of these comparisons with
the canonical homology and degree-zero recovery isomorphisms, remain later
construction obligations. Scalar change, tower limits, compact supports,
smooth equivariance, Galois actions, arithmetic coefficients and Harris
specialization also remain separate work.
