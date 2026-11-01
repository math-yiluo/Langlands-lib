# Constructed inverse image and restriction along an etale morphism

This module identifies the arbitrary-morphism constructions from
`EtaleDirectImage` and `EtaleInverseImage` with the previously constructed
functors along an etale morphism. These are isomorphisms of actual
functors, obtained from proved adjunctions.

The base map is `f : Z ⟶ X` with `[Etale f]`, and both schemes have
universe `u`. The first two constructions allow an arbitrary coefficient
category `A : Type uA` with morphisms in universe `vA`. The inverse-image
comparison and finite-limit preservation use `ModuleCat.{u} R`, where
`R : Type u` is a commutative ring. No field, finiteness, finite-type,
Noetherian, coefficient-freeness or local-constancy hypothesis is imposed.

This is internal categorical infrastructure. Its provenance is the actual
composition/base-change adjunction on small etale objects, the resulting
sheaf adjunctions, and uniqueness of adjoints in Mathlib. It makes no new
external-literature claim.

## The geometric restriction/direct-image adjunction

Write `C_f : Z.Etale ⥤ X.Etale` for composition of the structural
morphism with `f`, and `P_f : X.Etale ⥤ Z.Etale` for actual scheme
base change. The existing
`EtalePullback.siteMapPullbackAdjunction f` is `C_f ⊣ P_f`.
Both functors are continuous for their small etale topologies.

`restrictionGeometricAdjunction f A` applies
`Adjunction.sheafPushforwardContinuous` to this site adjunction.
It gives

```text
EtalePullback.restriction f A
  ⊣ EtaleDirectImage.directImage f A.
```

Its left functor evaluates a sheaf on the composite structural
morphism to `X`; its right functor evaluates on actual geometric
base change to `Z`. The unit, counit, naturality and triangle
identities are induced from the site adjunction.

The older `EtalePullback.directImage f A` was constructed by
right Kan extension and is already right adjoint to the same
restriction functor. `rightKanDirectImageIsoGeometric` applies
`Adjunction.rightAdjointUniq` to those two adjunctions. It
identifies that earlier right-Kan direct image with the
geometric direct image, for the full stated coefficient scope.

## Constructed inverse image agrees with restriction

`EtaleInverseImage.inverseImage f R` was constructed by affine
restriction, an actual left Kan extension and target
sheafification, then transport across the dense-site
equivalence. Its existing `inverseImageAdjunction` makes it
left adjoint to `EtaleDirectImage.directImage f (ModuleCat R)`.

The preceding `restrictionGeometricAdjunction` has the same
right adjoint. Consequently `inverseImageIsoRestriction`
uses `Adjunction.leftAdjointUniq` to construct

```text
inverseImage f R ≅ EtalePullback.restriction f (ModuleCat R).
```

No choice of a comparison is supplied by the user. The isomorphism
is the one determined by the two actual adjunctions.

`inverseImage_etale_preservesFiniteLimits` transports the
existing finite-limit preservation of restriction through the
inverse of this isomorphism. Thus the constructed inverse image
preserves finite limits for etale base maps. Arbitrary base maps
are allowed by its earlier construction, but finite-limit
preservation for those maps is a separate proof obligation.

Identity and composition coherence of the arbitrary-map
construction, comparison with associated torsor coefficients,
algebraic-closure base change, support and derived
comparisons, and Harris specialization remain separate.
