# Local epsilon products of a global relation at the finite places other than `v`

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global argument
(1973, proof of Lemma 4.12) the product of the local epsilon factors of the global relation at a
finite place other than the distinguished one is `1`: at unramified places by Lemma 4.15, and at
the remaining places because the global characters are twisted by a character that is highly
ramified there (Lemma 4.16). This unit applies the standalone forms of these lemmas
(`BrauerKernel.StandaloneEpsilon`) to the local relation produced by `BrauerKernel.LocalRelation`.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. Fix number fields `k ⊆ E'`, a finite
index type `J`, integers `r j`, intermediate fields `K j` of `E'/k`, Hecke characters `Λ₁ j`,
`Λ₂ j` of `K j`, a finite place `z` of `k`, and a reciprocity family `eC` of `k_z` with
`NormalizedReciprocity (padicField z) eC`.

## Definitions

- `LocalPlaceRelation r K Λ₁ Λ₂ z eC`: the relation
  `Σ_{(j,u)} r_j · Ind_{(K_j)_u}^{k_z} ([weilCharacter e_u (Λ₁ j)_u] - [weilCharacter e_u (Λ₂ j)_u]) = 0`
  in the continuous exact virtual group of `W_{k_z}`, over the pairs of an index `j` and a place `u`
  of `K j` above `z`, with the transported candidates `e_u` of `eC`. This is the conclusion of
  `sum_induce_weilCharacter_eq_zero`.
- `placeEpsilonRatioProduct r K Λ₁ Λ₂ z ψz μ`: the product over the same pairs of
  `(ε((Λ₁ j)_u, ψz ∘ Tr, μ, 0) / ε((Λ₂ j)_u, ψz ∘ Tr, μ, 0)) ^ r_j`, Tate's local constants on the
  canonical packages `towerPadicField z u`.

## Results

- `quasicharacterAt_normComp_mul`: the component at `u` of `(α ∘ N) · Φ` is the component of `Φ`
  times `α_z` composed with the field norm of the canonical packages (`normComp_finiteComponent`,
  `localUnitNorm_eq_units_map_norm`).
- `placeEpsilonRatioProduct_eq_one_of_unramified` (**unramified places**): if the local relation
  holds, the characters are `Λ_i j = (α ∘ N) · Φ_i j` for some Hecke character `α` of `k`, every
  place of every `K j` above `z` has ramification index one, and the `Φ_i j` are unramified there,
  then the epsilon product is `1`. Proof: `prod_epsilon_ratio_eq_one_of_unramified` with
  `α_z`; the ramification indices agree by `ramificationIndex_towerPadicField_eq`, the components of
  `Φ` are unramified by `isUnramifiedQuasicharacter_quasicharacterAt`, and the decomposition is
  `quasicharacterAt_normComp_mul`.
- `lt_multiplicativeConductor_quasicharacterBase`: the conductor bound of `PlaceRamification` for
  the base package `padicField z`.
- `exists_bound_placeEpsilonRatioProduct_eq_one` (**ramified places**): for `ψz` and a conductor
  bound `Kb` there is `B` such that, for every `α` whose component at `z` has conductor exponent at
  least `B`, if the local relation holds and `Λ_i j = (α ∘ N) · Φ_i j` with conductor exponents of
  the components of `Φ_i j` at most `Kb`, the epsilon product is `1`. Proof:
  `exists_bound_prod_epsilon_ratio_eq_one_of_ramified`.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973), registered as
`deligne-1973-local-constants`, Lemmas 4.15 and 4.16 (printed pages 545–547) as used in the proof of
Lemma 4.12 (printed page 544). The unit only adapts the published standalone lemmas to completions
of number fields.
