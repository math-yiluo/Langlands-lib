# Geometric and restriction coefficient diagrams

This internal construction gives an actual equivalence between the existing
geometric coefficient category in `EtaleGeometricCoefficientDiagram` and the
restriction coefficient category in `EtaleCohomologyDiagramFunctor`, for a
contravariant scheme diagram whose transition maps are etale. Both categories
contain actual module sheaves on the small etale sites. The equivalence preserves
each sheaf and every component morphism, and transports the transition morphisms
through the already constructed inverse-image/restriction comparison.

## Inputs and conventions

Let `J : Type v` carry `Category.{w} J`, and let
`S : J ⥤ Scheme.{u}ᵒᵖ`. Write `X_i = (S.obj i).unop`. An arrow `a : i ⟶ j`
gives the scheme morphism `f_a = (S.map a).unop : X_j ⟶ X_i`. The module
assumes `Etale f_a` for every such arrow. Let `R : Type u` be any commutative
ring; module carriers are in universe `u`.

The geometric coefficient category uses `inverseImage f_a R`; the restriction
category uses `EtalePullback.restriction f_a (ModuleCat.{u} R)`. A transition
morphism need not be an isomorphism. There is no field, finiteness, Noetherian,
local-constancy, or derived-localization hypothesis on this equivalence.
In particular, importing the geometric diagram module does not add its later
localization hypotheses to these declarations.

The two categories' identity and composition constraints retain the actual
equalities coming from `S.map_id` and `S.map_comp`. The construction uses those
constraints, rather than treating the scheme diagram as strictly functorial
on the level of inverse-image functors.

## Comparisons of the diagram constraints

For an arrow `a`, `diagramInverseImageIsoRestriction R S a` abbreviates the
existing `inverseImageIsoRestriction f_a R`. Denote this natural isomorphism
by `c_a : g_a ≅ r_a`, where `g_a` is geometric inverse image and `r_a` is
restriction. Write `gamma_ab` and `delta_ab` for the geometric and restriction
composition constraints. At a sheaf `F` on `X_i`, the two main identities are

```text
c_id.hom(F) ≫ restrictionIdentity.hom(F) = geometricIdentity.hom(F)

gamma_ab.hom(F) ≫ c_(a≫b).hom(F)
  = g_b.map(c_a.hom(F)) ≫ c_b.hom(r_a(F)) ≫ delta_ab.hom(F).
```

`diagramInverseImageIsoRestriction_id` proves the first equation by combining
the existing equality-transport comparison for `S.map_id` with
`inverseImageIsoRestriction_id`. The composition theorem combines the
comparison for `S.map_comp` with `inverseImageIsoRestriction_comp`, then
evaluates the whiskered natural transformations at `F`.

`diagramInverseImageIsoRestriction_comp_inv` proves the corresponding inverse
formula

```text
delta_ab.hom(F) ≫ c_(a≫b).inv(F)
  = c_b.inv(r_a(F)) ≫ g_b.map(c_a.inv(F)) ≫ gamma_ab.hom(F).
```

Its proof cancels the invertible `c_(a≫b).hom(F)`, applies the forward
composition equation, and cancels the remaining inverse pairs through
functoriality. None of these identities is supplied as an extra input.

## Transport of actual coefficients

In the namespace `EtaleGeometricDiagram.CoefficientDiagram`,
`ofRestriction D` keeps the actual sheaf `D.obj i` at each vertex and sets

```text
(ofRestriction D).map a = c_a.hom(D.obj i) ≫ D.map a.
```

Its identity law is the first comparison equation. Its composition law uses
the forward composition equation, the restriction coefficient diagram's
composition law, and naturality of `c_b.hom` at `D.map a`.

Conversely, `toRestriction D` keeps the same actual sheaves and sets

```text
(toRestriction D).map a = c_a.inv(D.obj i) ≫ D.map a.
```

Its identity law cancels `c_id.inv` against the forward identity comparison.
Its composition law uses the inverse composition equation, the geometric
coefficient diagram's composition law, and naturality of `c_b.inv`.

`ofRestrictionFunctor` and `toRestrictionFunctor` both send a coefficient
morphism `alpha` to the family `alpha.app i` itself. Naturality of `c_a.hom`
and `c_a.inv` proves the required transition squares. Identities and
composition are preserved pointwise.

## Equivalence and evaluation

`geometricRoundTripIso D` identifies
`ofRestriction (toRestriction D)` with `D`;
`restrictionRoundTripIso D` identifies
`toRestriction (ofRestriction D)` with `D`.
Both directions of each isomorphism have the identity on `D.obj i` as their
component. Their transition squares follow by cancelling `c_a.hom` with
`c_a.inv`. Their inverse laws are the pointwise identity laws.

`restrictionEquivalence` is the equivalence from geometric coefficients to
restriction coefficients with functor `toRestrictionFunctor` and inverse
`ofRestrictionFunctor`. Its unit is the inverse geometric round-trip
isomorphism and its counit is the restriction round-trip isomorphism. Their
naturality and the triangle equation reduce to identities of actual sheaf
maps. No adjustment of the chosen unit or counit is needed.

`toRestrictionEvaluationIso i` and `ofRestrictionEvaluationIso i` record that
each transport commutes with evaluation at the actual vertex sheaf and its
morphisms. These are identity natural isomorphisms, since the corresponding
evaluation functors are definitionally equal.

## Provenance and remaining scope

The content is internal categorical assembly of the existing actual small-etale
module-sheaf categories, geometric inverse image, restriction, and their proved
comparison coherences. Its mathematical inputs are genuine sheaves and sheaf
maps with sheaf-level diagram laws; no cohomology or desired comparison theorem
is stored as input. It makes no new assertion from Harris or Berkovich.

The construction applies only when all transitions are etale. The geometric
coefficient category itself remains available for arbitrary scheme transitions.
Comparisons of derived-section, ordinary-cohomology and section diagram
functors are subsequent constructions. Scalar change, tower limits,
compact supports, smooth equivariance, Galois actions, arithmetic coefficient
sheaves and the Harris specialization also remain separate obligations.
