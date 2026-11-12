# Harris's level `K_p` with a varying factor at the distinguished place

Author: Worker 19.

This module defines Harris's level (4.1),
`K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`, of the unitary similitude group at a
degree-one place of the imaginary quadratic field. The open compact subgroup
`C_v` at the distinguished place varies; the subgroups `C^(j)` at the other
places are fixed. It is built on the product-form levels `splitPlaceLevel` of
`HarrisSplitPrimeFactorLevels`.

The module also shows that `K(N)_p` of `HarrisDivisionLevels` is the case
where `C_v` is the congruence level and every `C^(j)` is the maximal compact
subgroup. Finally, it makes `K_p` a functor of `C_v` on the level category of
`Langlands.Shimura.Levels`.

## Source

Harris (1999), Section 4, printed p. 309 (PDF p. 11): "write
`K(m)^p = K^{ℓ,p} × K_ℓ(m)`, with
(4.1) `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`.
Here `C_v ⊂ (𝒟_1)ˣ` is an open compact subgroup, which we allow to vary,
whereas `C^(j) ⊂ (𝒟_j)ˣ` will be fixed; we are implicitly identifying
(4.2) `GJ_p ⥲ ∏_j (𝒟_j)ˣ × ℚ_pˣ` as in [H2, Appendix, A.1]." Later on the
same page, `K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ`, and "`M̆_N` depends on
the factors `C^(j)` of (4.1)".

Harris (1997), Section 2, printed p. 89 (PDF p. 15): "For `j > 1`, we let
`C_v^(j)` denote the (unique) maximal compact subgroup of `GG(K_1^(j))`".

## Declarations

All declarations are in namespace `Langlands.Shimura`. Work in the setting of
`HarrisDivisionLevels`:

- `σ : SecondKindInvolution E K A` with `A` finite over `ℚ`;
- `ι : F →+* K` for the imaginary quadratic field `F`;
- a place `𝔭` of `F` above the rational place `v`, with bijective completion
  map `h𝔭`.

The places `w` of `K` above `𝔭` index the factors
`(K_w ⊗[K] A)ˣ = FactorUnits K A K_w` of `GG(ℚ_v)` (published
`splitPlacePoints`). Here `C` is a family of levels of the factors, `w₀` a
place above `𝔭` and `C₀` a level of the factor at `w₀`.

- `σ.distinguishedLevel ι v 𝔭 h𝔭 C w₀ C₀` is `σ.splitPlaceLevel` of the family
  `C` with its value at `w₀` replaced by `C₀` (`Function.update C w₀ C₀`).
  This is Harris's `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`, with `C_v = C₀` and
  `C^(j) = C w` for `w ≠ w₀`.
- `mem_distinguishedLevel`: a point `g` lies in `K_p` if and only if:
  - its `w₀`-component lies in `C₀`;
  - its component at every other `w` lies in `C w`;
  - its multiplier lies in `ℤ_vˣ`.
- `distinguishedLevel_mono`: `C₀ ⊆ C₁` implies `K_p(C₀) ⊆ K_p(C₁)`.
- `harrisLocalLevels_eq_update` and `harrisLevel_eq_distinguishedLevel`: when
  `K_w ⊗[K] A` is a division algebra at every `w`, the published
  `σ.harrisLevel` (Harris's `K(N)_p`) equals `σ.distinguishedLevel`. Here `C`
  is the family of maximal compact levels `placeMaximalCompactLevel` (the
  unique maximal compact subgroups `C^(j)` of Harris 1997) and `C₀` is the
  congruence level `placeCongruenceLevel`.
- `σ.distinguishedPoint ι v 𝔭 h𝔭 w₀` is the monoid homomorphism
  `(K_{w₀} ⊗[K] A)ˣ → GG(ℚ_v)` sending `h` to the point with component `h` at
  `w₀`, component `1` at every other place and multiplier `1`. It is the
  inverse of `splitPlacePoints` applied to `(Pi.mulSingle w₀ h, 1)`
  (`splitPlacePoints_distinguishedPoint`).
- `distinguishedPoint_conj_mem`: suppose `h⁻¹ k h ∈ C₁` for every `k ∈ C₀`.
  Then conjugation by the point of `h` maps `K_p(C₀)` into `K_p(C₁)`. The
  conjugation acts as `h` on the `w₀`-component and trivially on the other
  components and on the multiplier.
- `σ.distinguishedLevelFunctor ι v 𝔭 h𝔭 C w₀` is the functor
  `C₀ ↦ K_p(C₀)` from the published level category
  `CompactOpenLevel ((K_{w₀} ⊗[K] A)ˣ)` to `CompactOpenLevel (GG(ℚ_v))`.
  Arrows of the level category are elements `h` with `h⁻¹ C₀ h ⊆ C₁`. An
  arrow `h` goes to the arrow given by `distinguishedPoint h`. Identities and
  composition are preserved because `distinguishedPoint` is a monoid
  homomorphism (`distinguishedLevelFunctor_obj`,
  `distinguishedLevelFunctor_map_element`).

## Scope

- **Generic algebra.** The module works with the published `GG` of a
  second-kind involution on `A`. Harris states (4.1) for `GJ` and its algebra
  `𝒟`; it applies by taking `A` to be `𝒟` with its involution.
- **Choices left as inputs.** The fixed subgroups `C^(j)` are arbitrary
  inputs, as in Harris 1999; Harris 1997's choice, the maximal compact
  subgroups, is the instance used for `K(N)_p`. The distinguished place `w₀`
  is also an input. The companion candidate `HarrisCMTypePlaces` relates it to
  Harris's `v ∈ Φ_p`; this module does not import it.
- **Not covered.** The global levels `K(N, m) = K(N)_p × K(m)^p` are in the
  published `HarrisInnerFormLevels` and `HarrisSplitPrimeLevels`. The action
  on the Shimura variety or the Rapoport-Zink space is not treated.

## Provenance

Derived from Harris (1999), Section 4, printed p. 309, and Harris (1997),
Section 2, printed p. 89, both read in the original. Updating a family of
local levels at one place, and building the functor through the published
level category, are implementation choices.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.

Formal dependencies: the published
`Langlands.Shimura.Unitary.HarrisDivisionLevels` and through it
`HarrisSplitPrimeFactorLevels`, `HarrisSplitPrimeFactors` and
`Langlands.Shimura.Levels`, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0. The Mathlib
results used include `Function.update`, `MonoidHom.mulSingle`,
`MonoidHom.inl` and `Pi.mulSingle_eq_same`.
