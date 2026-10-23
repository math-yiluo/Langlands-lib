# Geometric functoriality of equivariant étale pullback

This module constructs natural identity and composition comparison isomorphisms
for the canonical equivariant pullback on small-étale module sheaves. Under
these comparisons, the existing geometric maps on ordinary cohomology and
sections preserve identity and composition. All declarations are in
`Langlands.Geometry.EtaleCohomologyAction`.

## Inputs and conventions

The schemes `X`, `Y`, and `Z` and the commutative coefficient ring `R` have
universe `u`. The group `G` has independent universe `w`. Its algebraic actions
are supplied as `ρ : G →* (Aut X)ᵐᵒᵖ`, `τ : G →* (Aut Y)ᵐᵒᵖ`, and
`υ : G →* (Aut Z)ᵐᵒᵖ`. The opposite-automorphism convention is the one in
`EtaleCohomologyAction`: `aut ρ (g * h)` executes `aut ρ g` and then `aut ρ h`.
No topology on `G` is required.

For composition, the inputs are actual étale maps `f : Y ⟶ X` and `k : Z ⟶ Y`
with the scheme equations

```text
hf(g): f ≫ aut(ρ,g).hom = aut(τ,g).hom ≫ f,
hk(g): k ≫ aut(τ,g).hom = aut(υ,g).hom ≫ k.
```

`equivariantMap_id` supplies the identity scheme equation, and
`equivariantMap_comp` derives the equation for `k ≫ f` by associativity and
`hf`, `hk`. The latter equation does not require étaleness; the pullback
constructions using it do.

Write `P_f` for ordinary restriction along `f`, `Q_f` for its published lift
`equivariantPullback R ρ τ f hf`, and `T_X(g)` for translation on sheaves.
The geometric comparison `C_f(g) = equivariantRestrictionIso ... g` has
orientation `T_X(g) ⋙ P_f ≅ P_f ⋙ T_Y(g)`. The action on `Q_f(F)` is
`C_f(g).inv(F) ≫ P_f(F.act g)`. All isomorphisms below are natural in the
coefficient sheaf.

## Identity comparison

Let `e : P_id ≅ Id` be the ordinary `restrictionId`. The lemma
`equivariantRestrictionIso_id` proves the equality

```text
C_id(g).inv(F) ≫ e(T_X(g)(F)) = T_X(g)(e(F)).
```

Its proof evaluates both sheaf morphisms on each object of the actual small
étale site. The shared `restrictionCongr_inv_component` lemma from
[EtaleEquivariantPullback](EtaleEquivariantPullback.md) expresses the inverse equality-transport
comparison as the presheaf image of the opposite of the forward `Over.mapCongr`
component. After unfolding restriction and translation, presheaf functoriality
reduces the identity to the identity underlying scheme maps of `Over.mapId`,
`Over.mapComp`, and `Over.mapCongr`.

`equivariantPullbackId` lifts `e` to `Q_id ≅ Id` in the category of equivariant
sheaves. Naturality of `e` at `F.act g`, followed by the preceding equality,
proves equivariance of its forward map. The published
`TranslationAction.Equivariant.mkIso` constructs the inverse equivariant map
and the inverse laws. Naturality in an equivariant coefficient morphism is
inherited from `e`. The lemma `equivariantPullbackId_hom_app_hom` identifies
its underlying map exactly with `restrictionId.hom.app F.obj`.

## Composition comparison

Let `d : P_f ⋙ P_k ≅ P_(k≫f)` be `restrictionComp f (ModuleCat R) k`.
The lemma `equivariantRestrictionIso_comp` proves

```text
C_k(g).inv(P_f(F)) ≫ P_k(C_f(g).inv(F)) ≫ d(T_X(g)(F))
  = T_Z(g)(d(F)) ≫ C_(k≫f)(g).inv(F).
```

As in the identity case, its implementation works on site components, unfolds
the three restriction squares, combines presheaf maps, and identifies the
underlying identity scheme maps. Thus this coherence equation is proved from
the geometry; it is not an extra input.

`equivariantPullbackComp` lifts `d` to

```text
Q_f ⋙ Q_k ≅ Q_(k≫f).
```

To prove equivariance, expand the two successive induced actions, use
naturality of `d` at `F.act g`, and apply the preceding coherence equation.
The inverse and inverse laws come from `Equivariant.mkIso`; naturality in
coefficients comes from `d`. The lemma
`equivariantPullbackComp_hom_app_hom` identifies the forward map with the
ordinary `restrictionComp.hom.app F.obj`.

## Cohomology and section laws

For every degree `q : ℕ`, write `H_X^q` for the published functor from
equivariant sheaves to `G`-actions on ordinary small-étale module cohomology,
and `a_f^q` for `equivariantPullbackCohomology ... q`.
The following are equalities of morphisms of `G`-actions:

* `equivariantPullbackCohomology_id` proves
  `a_id^q(F) ≫ H_X^q(e(F)) = id`.
* `equivariantPullbackCohomology_comp` proves
  `a_f^q(F) ≫ a_k^q(Q_f(F)) ≫ H_Z^q(d(F)) = a_(k≫f)^q(F)`.
* `equivariantPullbackSections_id` and
  `equivariantPullbackSections_comp` prove the same two laws for the ordinary
  section-action functors and `equivariantPullbackSections`.

Each proof uses extensionality of action morphisms. The published underlying-map
formulas and the new comparison formulas reduce the goal to the corresponding
ordinary identity or composition law in `EtaleDerivedPullbackFunctoriality`.
No cohomology compatibility is assumed as input.

## Provenance and scope

This is an internal derived construction from the published
`EtaleEquivariantPullback`, `EtalePullback`,
`EtaleDerivedPullbackFunctoriality`, and `TranslationEquivariantCategory`
modules, together with Mathlib's `MorphismProperty.Over` site comparisons.
It does not claim to transcribe a named theorem from Harris or Berkovich.

The schemes, group actions and equivariant étale morphisms remain supplied
geometric inputs. The result constructs the two natural comparisons and their
cohomology and section laws. It does not package a pseudofunctor or prove the
triangle and pentagon coherence laws for repeated geometric comparisons.
It does not construct an analytic site, a Shimura tower, smooth actions,
compactly supported cohomology, traces, or the specialization required by
Harris. These remain separate obligations in the larger framework.
