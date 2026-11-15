# Standard local data, coverings by levels, and existence of levels

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusStd`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusLevel` and the published `MurreLocalToGlobalReduction`.

For a point `w` of `Spec (R'/𝔍)`:

- `primeOf 𝔍 w` is the prime `P_w` of `R'` below `w`, with an `IsPrime`
  instance;
- `Ow 𝔍 w` is the local ring `O_w = R'_{P_w}` (`Localization.AtPrime`);
- `le_primeOf`: `𝔍 ⊆ P_w`.

## Standard local data (section `Std`)

- `std_ne_top` / `isLocalRing_std`: let `𝔞 ⊆ P_w` and `𝔟 ⊆ (𝔍 + 𝔞)O_w`. Then
  `𝔟` is proper and `O_w/𝔟` is local. Indeed `(𝔍 + 𝔞)O_w ⊆ P_w O_w`, the
  maximal ideal.
- `stdDatum` is the standard local datum `O_w/𝔟` at `w`. Its inputs are:
  - a level `ρ : R' → D` that is an epimorphism of rings (ring maps out of `D`
    are determined by their composite with `ρ`);
  - an ideal `𝔞 ⊆ ker ρ`;
  - `𝔟` with `𝔍O_w ⊆ 𝔟 ⊆ (𝔍 + 𝔞)O_w` and `O_w/𝔟` local;
  - `δL : D → O_w/𝔟` with `δL ∘ ρ = (R' → O_w → O_w/𝔟)`;
  - a structure morphism `f`.

  Its `ℓ` is the map `R'/𝔍 → O_w/𝔟` induced by `R' → O_w`. The properties:
  - `comm`: `Ideal.quotientMap_comp_mk`.
  - `comap_eq`: the preimage of the maximal ideal of `O_w/𝔟` in `O_w` is
    maximal, and its preimage in `R'` is `P_w`
    (`Localization.AtPrime.under_maximalIdeal`). Cancel the surjection
    `R' → R'/𝔍`.
  - `univ`: let `C` be local with `γ : R'/𝔍 → C`, `δ' : D → C`,
    `γ ∘ mk = δ' ∘ ρ` and `γ⁻¹(𝔪_C) = w`. Elements of `R'` outside `P_w` go
    to units of `C`. So `γ ∘ mk` extends to `β' : O_w → C`
    (`IsLocalization.lift`). `β'` kills `𝔟`: it kills `𝔍`, and kills `𝔞`
    because `𝔞 ⊆ ker ρ`. It descends to `μ : O_w/𝔟 → C`, and:
    - `μ ∘ ℓ = γ`;
    - `μ ∘ δL = δ'`, since both agree after composing with the epimorphism
      `ρ`;
    - `μ` is local: if `μ(r/s)` is a unit, then `γ(mk r)` is a unit, so
      `r ∉ P_w` and `r/s` is a unit (`IsLocalization.AtPrime.isUnit_mk'_iff`).
  - `gen`: `r/s = δL(ρ r)/δL(ρ s)` (`IsLocalization.mk'_spec`).

## Coverings (section `Cover`)

- `killAt_of_comap`: the lifting condition `KillAt ξ w A β` only involves maps
  `β` with `β⁻¹(𝔪_A) = P_w`. A lifting problem at `w` forces this equality:
  the ring map `γ₀` of `u₀` satisfies `γ₀⁻¹(𝔪) = w` and
  `γ₀ ∘ mk_𝔍 = mk_J ∘ β`, and `mk_J⁻¹(𝔪_{A/J}) = 𝔪_A`.
- `killAt_of_localization`: let `P` be a prime with `P_w ⊆ P`. If
  `KillAt ξ w A (δ' ∘ (R' → R'_P))` holds for all `δ' : R'_P → A`, then
  `KillAt ξ w A β` holds for all `β`. Elements outside `P` lie outside `P_w`
  and go to units, so `β` factors through `R'_P`.
- `killAt_of_quotient`: let `I ⊆ P_w` and `A` local artinian. If
  `KillAt ξ w A (δ' ∘ (R' → R'/I^{n+1}))` holds for all `n ≥ n₀` and all
  `δ'`, then `KillAt ξ w A β` holds. `β(I) ⊆ 𝔪_A`, and `𝔪_A^N = 0` for some
  `N`. So `β` kills `I^{n+1}` for `n = max n₀ N`
  (`isArtinianRing_iff_isNilpotent_maximalIdeal`).

## Existence of levels (section `Existence`)

- `nonempty_level_localization`: suppose the base change of `F` to every
  `Spec 𝒪_{Spec R,s}` satisfies `UnramifiedRepresentable`. Then there is a
  level for `R' → R'_P` for every prime `P` of `R'`. The morphism
  `Spec R'_P ⟶ Spec R` sends the closed point to `s = P ∩ R`, so it factors
  through `Spec 𝒪_{Spec R,s}` (`Charts.exists_comp_fromSpecStalk`). Then:
  - the base change along a composite is the iterated base change
    (`LocalToGlobal.baseChangeCompIso`);
  - `UnramifiedRepresentable` is stable under base change
    (`LocalToGlobal.unramifiedRepresentable_baseChange`).
- `nonempty_level_quotient`: suppose the base change of `F` to every
  `Spec (R/I)` with `I ≠ 0` satisfies `UnramifiedRepresentable`. Then there is
  a level for `R' → R'/J` for every `J = I R'` with `I ≠ 0`. The morphism
  `Spec (R'/IR') ⟶ Spec R` factors through `Spec (R/I)`, and the same two
  facts apply.
