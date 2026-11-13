# Characters of generators at the distinguished place of a global realization

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, proof of Lemma 4.12, printed page 544), the local characters of a relation over a
p-adic field `F` are the local components at the distinguished place `v` of global characters
built from a Galois realization `K' / k` of a finite Galois extension `K / F`. This unit proves
that statement for one generator character in the present setting. It uses the realization data of
`BrauerKernel.RealizationField`, the conjugation comparison of `BrauerKernel.ConjugateTransport`,
and the properties of a local relative Weil map; it does not construct that map.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. The setting is that of
`RealizationField`: number fields `k ⊆ K'` (in `Type`, `K' / k` Galois), a place `v` of `k`,
`F : PadicField (residuePrime v)`, a normal `K : Extension F`, `θ : Gal(K'/k) ≃ Gal(K/F)`, a place
`w` of `K'` over `v`, ring isomorphisms `φ : k_v ≃ F` and `ψ : K'_w ≃ K` (continuous, `φ⁻¹`
continuous), `hcomp` and `hθ`. For `L ⊆ K`, `𝕃 = realizationSubfield K θ L` and `u` is a place of
`𝕃` between `v` and `w`. `E = towerPadicField v u` is the `ℚ_p`-package of `𝕃_u`, `f =
realizationBaseAlgHom v u φ hφ' : F → E`, and `σ_g = realizationGeneratorEquiv … : E ≃ L`.

## Norms

- `norm_eq_topologicalData_normalizedAbs`: on a completion `𝕃_u` of a number field, Mathlib's norm
  equals the residue-normalized absolute value of the completion-topology realization
  `topologicalData u`. Both are `N(u)^{log v(x)}`: Mathlib's `FinitePlace.norm_def` with base
  `N(u)`, and `normalizedAbs = q^{-ord}` with `q = N(u)` (`HeckeEulerProduct.residueCardinality_eq`)
  and `ord = -log v` (`topologicalData_discreteValuation`).
- `norm_eq_normalizedAbs_padicFieldAt`: the same with the canonical package `padicFieldAt u h` for
  any `h : residuePrime u = p`. Proof: substitute `h`; the normalized absolute value does not depend
  on the realization (`normalizedAbs_eq_canonicalNorm_pow_degree`).

## The conjugating Weil element

- `realizationClosureEmbedding`: the embedding `A : K'_w → \bar F`, Mathlib's chosen closure
  isomorphism over `f` (inverted) after the published `completionClosureEmbedding u w`.
  `realizationClosureEmbedding_completionMap`: on `𝕃_u` it is `extensionFieldEmbedding F E f`.
- `realizationClosureAlgHom`: `A ∘ ψ⁻¹ : K → \bar F` as an `F`-algebra map. It fixes `F` because
  `ψ⁻¹` maps `a ∈ F` to the image of `φ⁻¹ a` (`realization_completionMap`), the completion maps
  compose, and `extensionFieldEmbedding_comp`.
- `exists_projection_realizationClosureEmbedding`: there is `τ ∈ W_F` whose Galois projection
  carries `A` to `ψ`: `τ (A z) = ψ z` for all `z ∈ K'_w`. Proof: `K / F` is normal, so `A ∘ ψ⁻¹`
  restricts to an automorphism `α` of `K` (Mathlib's `AlgHom.restrictNormal'`); choose `τ` with
  restriction `α⁻¹` (`galoisRestriction_surjective`).

## Galois comparison

- `galoisRestriction_conj_eq_of_closure` (abstract form): let `j : K' → K_w` be a ring map,
  `ψ : K_w ≃ K` with `θ σ (ψ (j x)) = ψ (j (σ x))`, `ĵ : K_w → \bar E`, `τ ∈ W_F` with
  `τ (Λ⁻¹ (ĵ z)) = ψ z` (`Λ` the closure isomorphism over `f`), `y ∈ W_E` and `ρ ∈ Gal(K'/k)` with
  `ĵ (j (ρ x)) = y (ĵ (j x))`. Then the restriction of `τ y τ⁻¹` to `K` is `θ ρ`. Proof: on
  `ψ (j x)`, `τ⁻¹` gives `Λ⁻¹ (ĵ (j x))`; the image of `y` in `G_F` acts as `Λ⁻¹ y Λ`
  (`extensionClosureLift_galoisMap`); the hypothesis on `ρ` and on `τ` give `ψ (j (ρ x))`. Hence
  `θ⁻¹` of the restriction agrees with `ρ` on `K'`, by injectivity of `ψ ∘ j` and `hθ`.
- `galoisRestriction_conj_extensionWeilMap`: the concrete case. If `ι : W_{𝕃_u} → W_{K'/𝕃}`
  satisfies the projection clause of a local relative Weil map (the action of the projection of
  `ι g` on `K'` is the action of `g` through `completionClosureEmbedding u w`), then the restriction
  of `τ y τ⁻¹` to `K` is `θ` of the projection of `ι y`, viewed in `Gal(K'/k)`.

## The characters

`fieldCharacter_eq_realizationTransport`: let `e` be a normalized family, `χ` a field character of
`L`, `t ∈ ℂ` and `θL` a character of `galoisImage F K L` with
`θL ∘ toGaloisImage = twistedWeilCharacter F e L χ t` (the form of a Galois type decomposition).
Let `ι : W_{𝕃_u} → W_{K'/𝕃}` satisfy the projection clause above and have transfer
`(rec_{e'} y)⁻¹` at `u`, with `e' = extensionReciprocityCandidate F E f e`. Let `α` be a Hecke
character of `k` with trivial component at `v`, and `Θ` a Hecke character of `𝕃` whose reciprocity
character `continuousReciprocityCharacter c 𝕃 K' Θ` sends `x` to `θL (θ (projection x))`. Then

`χ = ConductorTransport.quasicharacter E L σ_g (quasicharacterAt u _ ((α ∘ N) · ‖·‖^t · Θ)_u)`.

Proof. Take `τ` as above; `conj_extensionFiniteIntermediate_field` gives `τ(L'') = L`. A unit `x`
of `L` is `σ_g (rec_{e'} y)` for some `y ∈ W_E` (`rankOne_reciprocityUnits_surjective`), and
`reciprocityUnits_conj_extension` gives `x = rec_{e,L}(W)` with `W = τ y τ⁻¹`. On the left,
`χ x` is the Weil character of `χ` at `W`, which is `ω_t(W) · θL(W)`
(`weilCharacter_eq_twisted` and the hypothesis on `θL`), and
`ω_t(W) = |x|_L^t` (`character_eq_norm_exp`, using normalization). On the right, the value at
`σ_g⁻¹ x = rec_{e'} y` splits by `finiteComponent_mul`: the factor of `α ∘ N` is
`α_v(N rec_{e'} y) = 1` (`normComp_finiteComponent`); the factor of `‖·‖^t` is
`exp (t log ‖rec_{e'} y‖) = |rec_{e'} y|_E^t = |x|_L^t` (`normPower_finiteComponent`,
`norm_eq_normalizedAbs_padicFieldAt`, `CanonicalTransport.normalizedAbs_map`); the factor of `Θ`
is the reciprocity character of `Θ` at `ι y` (`continuousReciprocityCharacter_apply_of_transfer_eq`
with the transfer clause), which is `θL` at `θ` of the projection of `ι y`, and this is
`toGaloisImage W` by `galoisRestriction_conj_extensionWeilMap`.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973), registered as
`deligne-1973-local-constants`, proof of Lemma 4.12 (printed page 544, PDF page 44): a subgroup of
`Gal(K'/K) = Gal(K'_v/K_v)` defines a local field and a global field, and a character of it is read
on both sides. This unit makes that identification explicit for the actual reciprocity families,
local relative Weil maps and Hecke characters of the Library.
