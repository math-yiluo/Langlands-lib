# Harris's (4.5) for compact levels of a definite group

Author: Worker 19.

The module `HarrisLevelFreeSmall` proves Harris's hypothesis (4.5) from two
conditions, `RationalFiniteOrder` and `LevelTorsionFreeAt`, and assumes the
first. The module `PositiveArithmeticFinite` proves that, when the real
scalar extension of the involution is positive, rational similitudes lying
in a conjugate of a compact level have finite order. This module combines
the two. For a positive involution, (4.5) holds as soon as the factors of
the level are compact and the away level is torsion-free at one place.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "We strengthen (3.6)
by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is
sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`." Here `K^{ℓ,p}` and `K_ℓ` are factors of the
open compact level `K` of Section 3, and `C_p` is compact (p. 310: "fix a
compact open subgroup `K_p ⊂ GJ_p` contained in a fixed maximal compact
subgroup `C_p`"). The group `GJ` is definite: Section 1, printed p. 301,
requires `J_∞ ≅ ∏_{σ ∈ Σ_E} U(n)`.

## Setting

Declarations are in namespace `Langlands.Shimura.DefiniteForms`.

- `σ : AlgebraInvolution ℚ A`, with `A` finite over `ℚ`. `GJ(ℚ)` is
  `σ.similitudes` and `GJ(A_f)` is `σ.FiniteAdelicPoints`. Definiteness is
  the hypothesis `hpos : (σ.baseChange ℝ).IsPositive` (the published
  positivity predicate of Worker 57).
- `n ≠ 0` and `e = σ.finiteAdelicPointsSplit n hn` splits
  `σ(A_f) ≃ₜ* σ(∏_{v ∣ n} ℚ_v) × σ(A_f^n)`. `splitLevel σ n hn U L` is the
  level `e⁻¹ (U × L)`, `DividingLevelFree` is (4.5), and
  `HarrisDividingLevelFree` is its case `n = ℓ p` with
  `U = pairLevel K_ℓ C_p`, all from the published
  `HarrisDividingLevelFree`.
- `RationalFiniteOrder` and `LevelTorsionFreeAt` are the two conditions of
  `HarrisLevelFreeSmall`, and `primeToLocalMap σ n v` is the component of
  `σ(A_f^n)` at a place `v` not dividing `n`, from the same module.

## Declarations

- `RationalFiniteOrder.of_isPositive`: if `σ ⊗ ℝ` is positive, every
  compact level `K` satisfies `RationalFiniteOrder`. This is
  `isOfFinOrder_of_conj_mem` from `PositiveArithmeticFinite`.
- `isCompact_splitLevel`: `e⁻¹ (U × L)` is compact when `U` and `L` are,
  because `e` is a homeomorphism and `U × L` is compact.
- `levelTorsionFreeAt_splitLevel`: let `v` be a place not dividing `n` and
  `W` a subgroup of `σ(ℚ_v)` whose only element of finite order is `1`. If
  the component at `v` of every element of `L` lies in `W`, then
  `e⁻¹ (1 × L)` satisfies `LevelTorsionFreeAt` at `v`. The component at `v`
  of `k ∈ e⁻¹ (1 × L)` is the component of `(e k).2 ∈ L`
  (`primeToLocalMap_finiteAdelicPointsSplit`).
- `DividingLevelFree.of_isPositive`: if `σ ⊗ ℝ` is positive, `U` and `L` are
  compact, and `e⁻¹ (1 × L)` is torsion-free at a place `v` not dividing
  `n`, then (4.5) holds: `U` acts without fixed points on
  `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`. It applies
  `DividingLevelFree.of_levelTorsionFreeAt` with the first two lemmas.
- `isCompact_pairLevel`: for distinct primes `ℓ` and `p`, Harris's
  `K_ℓ × C_p` (`pairLevel`) is compact when `K_ℓ` and `C_p` are. By the
  published `pairLevel_eq_comap` it is the preimage of `K_ℓ × C_p` under the
  homeomorphism `pairPointsEquiv : σ(∏_{v ∣ ℓ p} ℚ_v) ≃ₜ* σ(ℚ_ℓ) × σ(ℚ_p)`.
- `HarrisDividingLevelFree.of_isPositive`: Harris's case. For distinct
  primes `ℓ` and `p`, if `σ ⊗ ℝ` is positive, `K_ℓ`, `C_p` and `K^{ℓ,p}` are
  compact, and `K^{ℓ,p}` is torsion-free at a place `v` containing neither
  `ℓ` nor `p`, then `K_ℓ × C_p` acts without fixed points on
  `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`.

## Scope

- **Positivity is a hypothesis.** Deriving the positivity of `σ ⊗ ℝ` from
  `J_∞ ≅ ∏ U(n)` for Harris's `GJ` is not done here.
- **Existence of small levels.** This module does not construct a subgroup
  `W` of `σ(ℚ_v)` without nontrivial elements of finite order, nor a compact
  open `K^{ℓ,p}` inside it; here torsion-freeness at one place is a
  hypothesis. The construction is in `TorsionFreeLevels` and
  `HarrisSmallLevels`.
- **Openness is not used.** Only compactness of `K_ℓ`, `C_p` and `K^{ℓ,p}`
  is needed.
- **Adelic setting.** As in `HarrisDividingLevelFree`, Harris's
  `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}` is read as `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`.

## Provenance

The source is Harris (1999), Sections 1 and 4, printed pp. 301 and 310,
read in the original (rendered pages). The reduction of (4.5) to the two
conditions is that of `HarrisLevelFreeSmall`, and the finite-order property
for positive involutions is that of `PositiveArithmeticFinite`. The
combination and the compactness lemmas are written for this module.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- `Langlands.Shimura.Unitary.HarrisLevelFreeSmall` (`RationalFiniteOrder`,
  `LevelTorsionFreeAt`, `primeToLocalMap`,
  `primeToLocalMap_finiteAdelicPointsSplit`,
  `DividingLevelFree.of_levelTorsionFreeAt`,
  `HarrisDividingLevelFree.of_levelTorsionFreeAt`), from candidate
  `7c0a7e9b-59ea-41f0-bed4-cd80fcd887f6`;
- `Langlands.Shimura.Unitary.PositiveArithmeticFinite`
  (`AlgebraInvolution.isOfFinOrder_of_conj_mem`), from candidate
  `86a1bf69-cdc3-42a2-80dd-390814d5926d`;
- the published `Langlands.Shimura.Unitary.HarrisDividingLevelFree`
  (`splitLevel`, `mem_splitLevel`, `pairLevel`, `DividingLevelFree`,
  `HarrisDividingLevelFree`) and `Langlands.Shimura.Unitary.HarrisPairPoints`
  (`ellPlace`, `primePlace`, `pairPointsEquiv`, `pairLevel_eq_comap`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
  particular `Homeomorph.isCompact_preimage` and `IsCompact.prod`.
