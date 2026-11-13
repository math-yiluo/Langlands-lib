# Transport maps along the identity and twisted transport data

## Purpose and provenance

This file proves two further laws for the transport maps `sheafMap` of
`EtaleTransportDatum` in
[EtaleAssociatedTransport](EtaleAssociatedTransport.md). It is an internal,
derived construction: no theorem from the literature is assumed or
transcribed. The laws are needed to identify the transport maps of Harris's
coefficient systems (see
[HarrisTaylorCMLevelTransportLaws](../PEL/HarrisTaylorCMLevelTransportLaws.md)):

* along an identity of levels the transport map is the transition map of the
  coefficient system of that level (`sheafMap_id_transition`);
* translating by an element of the level does not change the transport map
  (`sheafMap_eq_of_twist`).

## Notation

The notation is that of
[EtaleAssociatedTransport](EtaleAssociatedTransport.md). All schemes, the
commutative ring `R`, module carriers and deck groups use universe `u`.
`constant Z` is the local notation for the constant-sheaf functor
`constantSheaf (Scheme.smallEtaleTopology Z) (ModuleCat R)`. For a cover `Y`
and a representation `M` of its deck group, `L_X(Y, M)` is
`(etaleAssociatedFunctor X Y).obj M` and `ι_Y(M)` its invariant inclusion
`etaleAssociatedInclusion X Y M`. `cP(a)` is `coverPullback _ a _`. `f^* Y` is
`(etaleTorsorPullbackFunctor f G).obj Y`. `K(a, c)` is
`etaleCrossCoverMap X ψ a c`. `M|_ψ` is `(Action.res (ModuleCat R) ψ).obj M`
and `Y'|_ψ` is `(Action.res X.Etale ψ).obj Y'`.

## Transport along the identity through a cover map

`EtaleTransportDatum.sheafMap_id_transition` concerns a transport datum `t`
along `𝟙 X`, from a cover `Y : Action X.Etale G` with representation
`M : Action (ModuleCat R) G` to a finite geometric torsor
`Y' : Action X.Etale H` (proof `hY'`) with representation `M'`. Its other
inputs are:

* a group homomorphism `ψ : G →* H`;
* an equivariant cover map `a : Y ⟶ Y'|_ψ`, such that
  `K(a, 𝟙 (M'|_ψ)) : L_X(Y', M') ⟶ L_X(Y, M'|_ψ)` is an isomorphism (an
  instance argument);
* an equivariant coefficient map `c : M ⟶ M'|_ψ`;
* a morphism `w : t.cover.V ⟶ Y.V` of etale `X`-schemes.

The hypotheses are:

* `hw : t.toSource ≫ etaleTorsorPullbackIdMap X Y = w`: the source cover map of
  `t`, followed by the identification of base change along the identity, is
  `w`;
* `ht : w ≫ a.hom = t.toTarget`: the target cover map of `t` factors through
  `a`;
* `hc : t.coefficient = c.hom`.

The conclusion is

```text
t.sheafMap hY' = (EtalePullback.restrictionId (ModuleCat R)).hom.app _
  ≫ (etaleAssociatedFunctor X Y).map c ≫ inv K(a, 𝟙 (M'|_ψ)).
```

So the transport map is the identification of the restriction along the
identity, followed by reduction of coefficients along `c` and the inverse of
the cover comparison of `a`. This is the form of the transition maps of
coefficient systems built from a diagram of covers and coefficient modules.

Proof. By `hom_ext` for `t` it suffices to compare both sides after
`ι_Y'(M') ≫ cP(t.toTarget)`. The left side is rewritten by
`sheafMap_inclusion`. In it, `λ_{𝟙}(Y, M)` is replaced by
`etaleConstantAssociatedPullback_id` and the same-group cross-cover equation
`etaleCrossCoverMap_id_inclusion_self` for the identification
`(etaleTorsorPullbackId X G).hom.app Y`. Then `coverPullback_comp`, `hw` and
`ht` turn the cover restrictions into `cP(w) ≫ cP(a.hom)`. On the right side,
`etaleCrossCoverMap_id_inclusion` for `a` cancels `inv K(a, 𝟙)` against
`K(a, 𝟙)` (`IsIso.inv_hom_id_assoc`), and `etaleAssociatedInclusion_natural`
moves the coefficient map `c` past the inclusion; `hc` identifies the two
coefficient maps. The remaining equation is the naturality
`coverPullback_natural` of `cP(w)` with respect to `(constant X).map c.hom`.

## Twisting a transport datum by a deck element

`EtaleTransportDatum.sheafMap_eq_of_twist` compares two transport data `t₁`
and `t₂` along the same etale `f : Z ⟶ X`, from `(Y, M)` to `(Y', M')`, where
`Y : Action X.Etale G`, `Y' : Action Z.Etale H` is a finite geometric torsor
(proof `hY'`), and `M`, `M'` are representations of `G` and `H`. Its other
inputs are a morphism `w : t₁.cover.V ⟶ t₂.cover.V` (not required to be
equivariant) and an element `g : G`. The hypotheses are:

* `hs : w ≫ t₂.toSource = t₁.toSource ≫ (f^* Y).ρ g`: up to `w`, the source
  cover map of `t₂` is that of `t₁` followed by the deck transformation of `g`
  on the base change of the source torsor;
* `ht : w ≫ t₂.toTarget = t₁.toTarget`;
* `hc : t₂.coefficient = M.ρ g⁻¹ ≫ t₁.coefficient`.

The conclusion is `t₂.sheafMap hY' = t₁.sheafMap hY'`.

Proof. By `hom_ext` for `t₁` it suffices to compare both sides after
`ι_Y'(M') ≫ cP(t₁.toTarget)`. The key input is the invariance of the
invariant inclusion under the deck action:

```text
ι_{f^* Y}(M) ≫ cP((f^* Y).ρ g) ≫ productSheaf((f^* Y).V).map((constant Z).map (M.ρ g⁻¹))
  = ι_{f^* Y}(M).
```

This is the Library's `inclusion_invariant` (in
[Associated](Associated.md)) for the cover `f^* Y`, the constant-sheaf
representation of `M` and the element `g⁻¹`, after `inv_inv`. Then
`t₁.sheafMap` is expanded by `sheafMap_inclusion`; `ht` and
`coverPullback_comp` rewrite `cP(t₁.toTarget)` as `cP(w) ≫ cP(t₂.toTarget)`;
`t₂.sheafMap` is expanded by `sheafMap_inclusion`; `coverPullback_natural`,
`coverPullback_comp`, `hs` and `hc` bring the composite to the left side of
the invariance equation, which closes the goal.

## Scope

Both laws are statements about arbitrary transport data. The application to
Harris's coefficient systems on the CM tower is in
[HarrisTaylorCMLevelTransportLaws](../PEL/HarrisTaylorCMLevelTransportLaws.md).
