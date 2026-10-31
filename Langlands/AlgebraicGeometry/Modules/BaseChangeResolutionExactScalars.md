# Canonical base change and scalar extension of cochain sections

This internal construction identifies the published canonical scalar
cohomology base-change map with the cohomology of an actual map of scalar
sections complexes, through specified compatible resolutions. It then gives
an invertibility criterion using acyclic resolutions. All schemes and rings
lie in an arbitrary universe `u`; all cochains and cohomology degrees are
indexed by `ℕ`.

## The scalar sections cochain map

Specify `φ : R → R'`, maps `f : X → Spec R`, `f' : X' → Spec R'`,
`g : X' → X`, and an equality
`w : g ≫ f = f' ≫ Spec.map φ`. Write `Γ_f` and `Γ_f'` for the actual
relative global sections functors, and `Ext_φ`, `Res_φ` for scalar extension
and restriction. No Cartesian-square hypothesis is imposed here.

For complexes `K` on `X`, `L` on `X'`, and an actual cochain map
`t : K → g_* L`, the preceding module `BaseChangeResolution` defines

`σ(t) : Γ_f(K) → Res_φ Γ_f'(L)`

as the composite of `Γ_f(t)` with the specified termwise pushforward and
base-ring comparisons. Define
`scalarResolutionSectionsBaseChangeMap φ f f' g w t` to be its adjunct
under the published extension/restriction-of-scalars adjunction on complexes:

`s(t) : Ext_φ Γ_f(K) → Γ_f'(L)`.

This is an actual cochain morphism, rather than a choice of maps on
cohomology. Its definition needs no resolution, flatness, or acyclicity
hypotheses. The reflexive component lemma
`scalarResolutionSectionsBaseChangeMap_f` identifies `s(t).f q` with the
ordinary module-adjunction adjunct of `σ(t).f q`. The lemma
`scalarResolutionSectionsBaseChangeMap_one_tmul` states

`s(t).f q (1 ⊗ x) = σ(t).f q x`.

Its proof evaluates the adjunction's inverse-equivalence identity at `x`
and uses Mathlib's tensor-generator formula for the hom-set equivalence.

The naturality lemma says that, for cochain maps `a : K → K'` and
`b : L → L'` satisfying `a ≫ t' = t ≫ g_*.map b`,

`Ext_φ Γ_f(a) ≫ s(t') = s(t) ≫ Γ_f'(b)`.

It applies naturality of the adjunction to the published naturality square
for `σ`.

## Flat scalar extension and cohomology

Assume `φ.hom.Flat`. Mathlib's
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat` supplies left
exactness of `Ext_φ`; it already preserves colimits. Both scalar functors
are thus exact, so the published exact-adjunction cohomology formula applies.
The lemma `scalarResolutionCohomologyMap_eq_homology` identifies the
previously defined adjunct on cohomology with

`scalarResolutionCohomologyMap t n`
` = (DerivedComparison.mapHomologyIso Ext_φ (Γ_f(K)) n).inv`
`   ≫ Hⁿ(s(t))`.

The inverse homology comparison has source `Ext_φ Hⁿ(Γ_f(K))` and target
`Hⁿ(Ext_φ Γ_f(K))`. The proof specializes
`ExactAdjunction.homologyAdjunct_eq` to the actual scalar adjunction and
`σ(t)`. Flatness is used for this homology comparison, not for defining
`s(t)`.

## Computing the canonical scalar base-change map

Let `M` be a module sheaf on `X`. In addition to the square and cochain map
above, suppose that

- `ε : M[0] → K` is a quasi-isomorphism;
- `η : (g^* M)[0] → L` is a quasi-isomorphism;
- the actual mapped augmentation `mapResolutionAugmentation g_* η`
  is a quasi-isomorphism;
- the augmentation square is
  `ε ≫ t = single₀.map (unit.app M) ≫ mapResolutionAugmentation g_* η`,
  where the unit is that of the actual sheaf pullback/pushforward adjunction;
- `hM` states that every positive higher direct image of `g^* M` under
  `g` is zero; and
- `φ.hom` is flat.

No termwise acyclicity of `K` or `L` is needed yet. The theorem
`resolutionComparison_scalarBaseChangeMap_homology` proves

`Ext_φ.map (resolutionComparison Γ_f ε n) ≫ scalarBaseChangeMap`
` = (mapHomologyIso Ext_φ (Γ_f(K)) n).inv`
`   ≫ Hⁿ(s(t)) ≫ resolutionComparison Γ_f' η n`.

Both sides are the specified morphism from `Ext_φ Hⁿ(Γ_f(K))` to
`Hⁿ_f'(g^* M)`. In particular, the left factor named
`scalarBaseChangeMap` is precisely the published canonical map, with its
published vanishing datum `hM`. The proof substitutes the preceding flat
cohomology identity into
`resolutionComparison_scalarBaseChangeMap` from `BaseChangeResolution`.
That published resolution formula supplies injective-pushforward
acyclicity from the proved theorem `pushforwardInjectiveAcyclic`.

## Invertibility from acyclic resolutions

Retain all the preceding hypotheses and assume additionally

- `hK : ∀ i q, IsZero (H^(q+1)_f(K.X i))`;
- `hL : ∀ i q, IsZero (H^(q+1)_f'(L.X i))`; and
- the actual scalar cochain map `s(t)` is a quasi-isomorphism.

Then `isIso_scalarBaseChangeMap_of_acyclicResolutions` proves that the
specified `scalarBaseChangeMap` is an isomorphism for every degree `n`.
The implemented proof invokes the published, proved theorem
`acyclicResolutionComparisonStatement` for each resolution. Applying it
to the chosen injective resolution and the canonical compatible lift makes
both resolution comparisons invertible. Quasi-isomorphism of `s(t)` makes
its degree-`n` homology map invertible. The preceding formula therefore
makes the composite of the scalar-extended source resolution comparison
and the canonical base-change map invertible. Cancelling that first
invertible factor proves the conclusion. The acyclic-resolution comparison
statement is discharged by its Library proof, not retained as a premise.

## Provenance and scope

All results are internal consequences of the specified constructions in
`BaseChangeResolution`, the published `ExactAdjunctionHomology` and
`AcyclicResolution.ComparisonProof`, and Mathlib's scalar adjunction,
flat-scalar exactness, and quasi-isomorphism identities. No new external
geometric assertion is introduced.

The criterion keeps the three augmentation quasi-isomorphisms, their
compatibility square, the higher-direct-image vanishing, termwise relative
acyclicity, and the quasi-isomorphism of `s(t)` as explicit hypotheses.
It does not construct a Čech resolution, prove localization base change,
or prove a relative cube statement. Its formulas identify actual canonical
maps and can be used once those geometric inputs have been supplied.
