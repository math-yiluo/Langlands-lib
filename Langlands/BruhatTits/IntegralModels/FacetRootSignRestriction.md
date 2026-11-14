# The facet sign formula as a root identity, and its restriction to subtori

Module `Langlands.BruhatTits.IntegralModels.FacetRootSignRestriction`.

## Setting

`R` is a local domain with fraction field `K`, `G` a group scheme over `K`,
and `κ` the residue field of `R`. For a KP relative component model `D` of
`G`, an integral torus `T : IntegralTorusData D S i` is a commutative
`R`-group scheme `T.torus` with an identification of its generic fibre
with `S` and a homomorphism `T.inclusion` into the neutral model of `D`
whose generic fibre is `i` under these identifications.
Its special fibre `T_s` is the base change of `T.torus` to `κ`.

## Content

### Maps of integral tori

Let `T : IntegralTorusData D S i` and `T' : IntegralTorusData D S' i'` be
integral tori of the same model, and `ρ : T.torus ⟶ T'.torus` a homomorphism
of `R`-group schemes.

- `IntegralTorusData.specialFibreMap T T' ρ : T_s ⟶ T'_s` is the base
  change of `ρ` to `κ`.
- `specialFibreMap_comp_specialFibreInclusion`: if `ρ ≫ T'.inclusion =
  T.inclusion`, then the special-fibre inclusion of `T` factors as
  `ρ_s` followed by the special-fibre inclusion of `T'`.
- `specialCharacter_comp`: base change of characters to `κ` is compatible
  with composition: `(ψ ∘ ρ)_s = ψ_s ∘ ρ_s` for every integral character
  `ψ` of `T'.torus`.
- `characterSpecialization_symm_apply`: the inverse of the Library's
  character specialization `X^*(S) ≃ X^*(T_s)` sends `χ` to the generic
  character of the integral character whose base change to `κ` is `χ`.
  This holds by definition.

### Restriction of the root-form sign formula

Let `φ : source ⟶ target` be a morphism of KP relative component models and
`Q` special-fibre quotient data of `target` (the quotient `π :
target_s ⟶ Q.quotient`). The Library defines
`φ.quotientTorusInclusion Q T : T_s ⟶ Q.quotient` and the reductive image
`φ.reductiveImage Q`, the schematic image of `φ_s ≫ π`. The accepted module
`FacetLieImageRoots` defines `φ.reductiveImageTorusMap Q T : T_s ⟶
φ.reductiveImage Q`.

- `reductiveImage_locallyOfFiniteType` (instance): the reductive image is
  locally of finite type over `κ` when `Q.quotient` is, because it is a
  subgroup scheme of `Q.quotient` through its inclusion.
- `specialFibreMap_comp_reductiveImageTorusMap` and
  `specialFibreMap_comp_quotientTorusInclusion`: if
  `ρ ≫ T'.inclusion = T.inclusion`, then `ρ_s` followed by the map of `T'_s`
  into the reductive image (respectively into `Q.quotient`) is the map of
  `T_s`.
- `roots_reductiveImageTorusMap_of_comp`: assume moreover that `T.torus`
  and `T'.torus` are split tori, `Q.quotient` is locally of finite type, and
  `σ : X^*(T.torus) → ℝ`, `σ' : X^*(T'.torus) → ℝ` are functions on the
  integral character lattices with `σ (ψ ∘ ρ) = σ' ψ` for all `ψ`. If
  the roots of `T'_s` in the reductive image are exactly the roots `χ` of
  `T'_s` in `Q.quotient` with `σ' (χ^int) ≥ 0`, then the same holds for
  `T_s` and `σ`. Here `χ^int` is the integral character with special fibre
  `χ` (via `specialCharacterEquiv`).

### The apartment sign formula as a root identity

`hasApartmentLieWeightSignFormula_iff_roots`: for a non-archimedean local
field `K`, valuation building data `B`, a split integral torus `T` of the
source model on the torus `B.S`, and subsets `Fa`, `Fa'` of the apartment,
the Library's `φ.HasApartmentLieWeightSignFormula B Q T hT Fa Fa'` holds if
and only if: for every `x ∈ Fa` and every `v` in the real cocharacter space
of `B.S` with `[v] + x ∈ Fa'`,

`roots (φ.reductiveImageTorusMap Q T) = {χ ∈ roots (φ.quotientTorusInclusion Q T) | 0 ≤ ⟨genericCharacter(χ^int), v⟩}`.

## Proofs

`specialFibreMap_comp_specialFibreInclusion` rewrites the special-fibre
inclusion of `T` with the hypothesis and uses that base change to `κ` is a
functor. `specialCharacter_comp` is the Library's
`characterLattice.baseChange_precomp`.

The two factorization lemmas unfold `reductiveImageTorusMap` and
`quotientTorusInclusion` and use the factorization of the special-fibre
inclusions.

`roots_reductiveImageTorusMap_of_comp` rewrites both sides with the two
factorizations and applies `roots_comp_eq_nonneg_of_roots_eq_nonneg` from
the helper module `Langlands.GroupScheme.Torus.SignedRootRestriction`, with
the special-fibre tori `T_s`, `T'_s` (split by base change of splitness) and
the sign functions `σ ∘ (·)^int` and `σ' ∘ (·)^int`. The required
compatibility is: for a character `ψ_s = (m₀)_s` of `T'_s`, the integral
character of `ψ_s ∘ ρ_s` is `m₀ ∘ ρ`. This is `specialCharacter_comp`
together with injectivity of `specialCharacterEquiv`; then `hσ` gives the
sign identity.

`hasApartmentLieWeightSignFormula_iff_roots` unfolds the definition and
rewrites its left side with `nonzeroLieImageWeights_quotientTorusInclusion`
(module `FacetLieImageRoots`). The Library's `relativeRoots` is `roots` by
definition, and `characterSpecialization_symm_apply` holds by definition, so
the remaining identification is `rfl`.

## Helper module

`Langlands/GroupScheme/Torus/SignedRootRestriction.{lean,md}` is submitted
with this module. Its theorem `roots_comp_eq_nonneg_of_roots_eq_nonneg`
says: for split tori `T`, `A` over a field, `ρ : T ⟶ A`, `b : A ⟶ H`,
`a : A ⟶ Q`, and sign functions with `sT (ψ ∘ ρ) = sA ψ`, if
`roots b = {ψ ∈ roots a | sA ψ ≥ 0}` then
`roots (ρ ≫ b) = {χ ∈ roots (ρ ≫ a) | sT χ ≥ 0}`. Its Markdown gives the
proof.

## Provenance

Internal infrastructure for the proof of
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Axiom 4.1.22(3)).
The descent argument proves the sign formula for a larger split torus of a
model over the maximal unramified extension and then restricts it to the
given torus. This module supplies the restriction step and states the
Library's sign formula in terms of root sets. It uses only the Library's
definitions, the accepted `FacetLieImageRoots` module and elementary
character functoriality, and makes no assertion from the literature beyond
them.
