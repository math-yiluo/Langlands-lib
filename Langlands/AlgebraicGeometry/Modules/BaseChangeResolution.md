# Canonical base change through compatible right resolutions

This internal construction computes the published canonical cohomology
base-change map, and its scalar-linear adjunct, using specified compatible
right resolutions. Schemes and commutative rings lie in an arbitrary universe
`u`, and the degree `n` is any natural number. All module sheaves, sections
functors, augmentations, and cochain maps below are the actual Library
constructions.

An augmentation is a cochain map `ε : M[0] → K`, with cochains indexed by
`ℕ`. It is a right resolution when it is a quasi-isomorphism. No assumption
that the terms of `K` are injective or acyclic is made here.

## Inverse pushforward comparison

Let `g : X' → X`, `f : X → Spec R`, and write `Γ_f` for
`relativeGlobalSections f`. Suppose that

- `ε : M[0] → K` and `η : N[0] → L` are quasi-isomorphisms;
- `mapResolutionAugmentation (Scheme.Modules.pushforward g) η` is also
  a quasi-isomorphism;
- `a : M → g_* N` and `t : K → g_* L` satisfy the actual augmentation
  square `ε ≫ t = single₀.map a ≫ mapResolutionAugmentation g_* η`;
- all positive higher direct images of `N` under `g` vanish; and
- the pushforward of each injective module sheaf on `X'` has vanishing
  positive relative cohomology under `f`.

Then `resolutionComparison_inv_pushforwardComparison` identifies

`resolutionComparison Γ_f ε n ≫ Hⁿ_f(a) ≫ inv(pushforwardComparison)`

with the cohomology of

`Γ_f(K) → Γ_f(g_* L) → Γ_(g ≫ f)(L)`

followed by `resolutionComparison Γ_(g ≫ f) η n`. The second cochain
arrow is the forward termwise `relativeGlobalSectionsCompIso`.
The vanishing hypotheses make the specified published pushforward comparison
invertible. The formula retains the separate quasi-isomorphism hypothesis
on the mapped arbitrary augmentation.

The proof combines `resolutionComparison_naturality` with
`resolutionComparison_compComparison`. After using the latter to compute
postcomposition with the forward pushforward comparison, it cancels that
invertible morphism to obtain the inverse formula.

## Changing the base ring

Let `φ : R → R'`, with maps `f : X → Spec R` and
`f' : X → Spec R'` satisfying `f = f' ≫ Spec.map φ`.
For any right resolution `ε : M[0] → K`,
`resolutionComparison_baseRingIso` identifies

`resolutionComparison Γ_f ε n ≫ relativeCohomologyBaseRingIso.hom.app M`

with the composite

`Hⁿ(Γ_f(K)) → Hⁿ(Res_φ Γ_f'(K))`
` → Res_φ Hⁿ(Γ_f'(K)) → Res_φ Hⁿ_f'(M)`.

The first arrow is the cohomology of the inverse termwise
`relativeGlobalSectionsBaseRingIso`; the second is the forward
`DerivedComparison.mapHomologyIso` for restriction of scalars; and the
last is restriction of scalars applied to the target resolution comparison.
Restriction of scalars is exact for every ring homomorphism. The proof
specializes the inverse exact-postcomposition resolution formula and the
published identification of the derived base-ring isomorphism.

## The sections cochain map

Now specify a commuting square

`g : X' → X`, `f : X → Spec R`, `f' : X' → Spec R'`,
`w : g ≫ f = f' ≫ Spec.map φ`.

For arbitrary complexes `K`, `L` and a cochain map `t : K → g_* L`,
`resolutionSectionsBaseChangeMap φ f f' g w t` is the actual cochain map

`Γ_f(K) → Res_φ Γ_f'(L)`.

Its three factors are `Γ_f(t)`, the forward termwise pushforward
composition comparison, and the inverse termwise base-ring comparison.
The lemma `resolutionSectionsBaseChangeMap_f` states that in degree `q`
the map is exactly

`Γ_f.map (t.f q) ≫ relativeGlobalSectionsCompIso.hom.app (L.X q)`
` ≫ relativeGlobalSectionsBaseRingIso.inv.app (L.X q)`.

This component identity is reflexive. The naturality lemma says that if
`a : K → K'` and `b : L → L'` satisfy `a ≫ t' = t ≫ g_*.map b`,
then applying `Γ_f` to `a` and then the map for `t'` equals the map for
`t` followed by `Res_φ Γ_f'(b)`. Its proof uses functoriality and
naturality of the two termwise comparisons. These constructions and
identities need no resolution or acyclicity hypotheses.

## Computing canonical cohomology base change

Take `N = g^* M`, and let `ε`, `η`, and `t` satisfy the three
quasi-isomorphism hypotheses above and the augmentation square with
`a` equal to the unit `M → g_* g^* M` of the actual sheaf
pullback/pushforward adjunction. Assume the positive higher direct images
of `g^* M` vanish and retain the injective-pushforward acyclicity hypothesis.
Then `resolutionComparison_baseChangeMap` proves

`resolutionComparison Γ_f ε n ≫ baseChangeMap`
` = Hⁿ(resolutionSectionsBaseChangeMap t)`
`   ≫ mapHomologyIso(Res_φ).hom`
`   ≫ Res_φ.map (resolutionComparison Γ_f' η n)`.

This is an equality with the specified published `baseChangeMap`, not
only an isomorphism between its source and target. The proof postcomposes
the inverse pushforward formula with the derived base-ring comparison,
substitutes the preceding base-ring resolution formula, and uses
functoriality of cohomology.

Define `scalarResolutionCohomologyMap φ f f' g w t n` to be the
extension/restriction-of-scalars adjunct of

`Hⁿ(resolutionSectionsBaseChangeMap t) ≫ mapHomologyIso(Res_φ).hom`.

It is an actual `R'`-linear map

`Ext_φ(Hⁿ(Γ_f(K))) → Hⁿ(Γ_f'(L))`

and requires no flatness hypothesis. The theorem
`resolutionComparison_scalarBaseChangeMap` proves

`Ext_φ.map (resolutionComparison Γ_f ε n) ≫ scalarBaseChangeMap`
` = scalarResolutionCohomologyMap t n`
`   ≫ resolutionComparison Γ_f' η n`.

For this scalar formula the injective-pushforward acyclicity is supplied
by the published theorem `pushforwardInjectiveAcyclic`; positive higher
direct-image vanishing for `g^* M` and all three augmentation
quasi-isomorphisms remain explicit. The proof applies Mathlib's
`Adjunction.homEquiv_naturality_right_square` to the established
semilinear equality. Thus the map on the left is exactly the published
`scalarBaseChangeMap`.

## Provenance and scope

These results are internal consequences of the published arbitrary-resolution,
pushforward, exact-postcomposition, base-ring, and scalar-adjunction
constructions, together with Mathlib's functoriality and naturality identities.
No external geometric assertion is introduced.

The formulas do not prove the augmentation hypotheses, invertibility of the
resolution comparisons, or invertibility of base change. In particular,
`scalarResolutionCohomologyMap` is defined as an adjunct on cohomology;
this file does not identify it with the cohomology of a scalar-extension
cochain map. It supplies no general Čech resolution, localization theorem,
or relative cube theorem.
