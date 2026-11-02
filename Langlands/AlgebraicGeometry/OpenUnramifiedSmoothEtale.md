# Component reduction for open unramified maps of smooth schemes

Author: Worker 57.

This module proves a conditional component reduction for actual Mathlib
schemes. Its principal theorem
`openUnramifiedSmooth_etale_of_dominantCriterion.{u}` takes the named
proposition `DominantUnramifiedEtaleStatement.{u}` as an explicit hypothesis.
It supplies no proof or default witness of that proposition.

The remaining inputs are a field `K : Type u`, schemes `X Y : Scheme.{u}`,
smooth morphisms `pX : X ⟶ Spec K` and `pY : Y ⟶ Spec K`, and an actual
morphism `f : X ⟶ Y` that is locally of finite type, formally unramified
and open on underlying spaces. The conclusion is `Etale f`. The theorem
does not assume that `f` commutes with the displayed structure maps.
Neither scheme is assumed connected, integral, nonempty, proper or
quasi-compact. The field has arbitrary characteristic and need not be
perfect or algebraically closed.

## Actual component restrictions

Smoothness over a field makes both schemes locally Noetherian.
The imported `LocallyNoetherianComponentSchemes` construction then gives
their actual open connected-component schemes, their open immersions and
the open cover by those components. For a component `c` of `X`,
`componentHom f c` is the restriction to the target component
`componentMap f c`. Its inclusion equation is

```lean
componentHom f c ≫ componentι Y (componentMap f c) =
  componentι X c ≫ f
```

`componentScheme_isIntegral_of_smooth` restricts the smooth structure map
to an actual component. The imported theorem `smoothDomainStalks`
provides domain stalks; the component is connected and locally Noetherian,
so `connectedLocallyNoetherianDomainStalksIntegral` proves its integrality.
Each indexed component is nonempty by the existing component construction.
An empty original scheme has an empty component index, which is handled
by its existing open cover.

`componentHom_isOpenMap` first proves openness after composing with the
target inclusion, using the displayed equation and the openness of the
source inclusion. The target inclusion is an open embedding, so its
open-map equivalence gives openness of the component restriction itself.

## Component criterion and return to the original map

For every integral target component, `smoothIntegralNormalStalks` proves
integral closedness of its actual structure-sheaf stalks. The existing
`geometricallyUnibranchIntegralScheme_of_stalks` converts this into
`GeometricallyUnibranchIntegralScheme` for that same component. This is
the normalization and residue-extension predicate used by the named
generic criterion.

The inclusion equation transfers local finite type and formal
unramifiedness to each component map by composition and cancellation.
Its source is nonempty and its target integral. Its open range is therefore
dense in the target, so the component map is dominant. Applying the supplied
`DominantUnramifiedEtaleStatement` proves etaleness of that component map.
Composition with the target open immersion gives etaleness of the
original map restricted to the source component. Zariski locality at the
source, applied to the actual component open cover, proves `Etale f`.

## Provenance and scope

This is an internal deduction from the named imported Library proofs,
the existing component constructions and the pinned Mathlib morphism and
topological facts. The generic proposition is the integral-source
specialization of Stacks Project Lemma 37.37.1, Tag 0GS8; its source
correspondence is recorded in `DominantUnramifiedEtaleStatement.md`.
The normal-stalk proof and its statement record the separate arbitrary-field
normality input. This module proves the component reduction, not the
generic criterion, Harris representability or source rigidity.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
