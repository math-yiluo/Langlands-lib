# Sufficiently small levels for Harris's definite group

Author: Worker 19.

Harris (1999) takes the away level `K^{ℓ,p}` "sufficiently small so that
(4.5)" holds. This module names that condition, `HarrisSufficientlySmall`,
and proves that it can be achieved below every compact open level for the
definite group of Harris's Section 3. That group is defined by an
involution of the second kind with the definite signature at every real
place. It combines `HarrisSmallLevels` (small levels exist for a positive
involution) with `DefinitePositivity` (the definite signature gives a
positive involution).

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "We strengthen (3.6)
by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is
sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`."

Harris (1999), Section 1, printed p. 301 (PDF p. 3): among the hypotheses
following (1.1), "`J_∞ = ∏_{σ ∈ Σ_E} U(n)`", expressed algebraically by
Worker 57's published `HasDefiniteSignature`.

## Setting

- In namespace `Langlands.Shimura.DefiniteForms`: `σ : AlgebraInvolution ℚ A`
  with `A` finite over `ℚ`; `DividingLevelFree`, `HarrisDividingLevelFree`,
  `splitLevel`, `ellPlace` and `primePlace` are as in the published
  `HarrisDividingLevelFree` and `HarrisPairPoints`. `vℓ` and `vp` are the
  places over the primes `ℓ` and `p`, and `hn : ℓ p ≠ 0`.
- In namespace `Langlands.Shimura.SecondKindInvolution`: `E` totally real,
  `K` a totally complex quadratic extension, `σ : SecondKindInvolution E K A`
  with `A` finite over `E` and `IsScalarTower ℚ E A`. Harris's `GJ` is the
  similitude group of `σ.rationalInvolution`.

## Declarations

- `DividingLevelFree.mono_right`: (4.5) passes to smaller away levels. If
  `g u` and `g` have the same class modulo `e⁻¹ (1 × L')` with `L' ≤ L`,
  they have the same class modulo `e⁻¹ (1 × L)` (published
  `splitLevel_mono`), so `u = 1`.
- `HarrisSufficientlySmall σ hn vℓ vp L : Prop`: for every compact
  `K_ℓ ≤ σ(ℚ_ℓ)` and compact `C_p ≤ σ(ℚ_p)`, Harris's (4.5)
  `HarrisDividingLevelFree σ (ℓ p) hn vℓ vp K_ℓ C_p L` holds. This is
  Harris's requirement on `K^{ℓ,p} = L`, quantified over the compact
  subgroups he uses (`K_ℓ` and the maximal compact `C_p`).
- `HarrisSufficientlySmall.mono`: smaller levels stay sufficiently small.
- `exists_harrisSufficientlySmall`: for a positive involution of a nonzero
  algebra and distinct primes `ℓ`, `p`, every compact open
  `L₀ ≤ σ(A_f^{ℓp})` contains a compact open sufficiently small level. This
  is `exists_harrisDividingLevelFree` from `HarrisSmallLevels`.
- `SecondKindInvolution.exists_harrisSufficientlySmall`: **Harris's
  sufficiently small levels exist for the definite group.** For `A` nonzero
  and finite over `E`, `HasDefiniteSignature σ n` and distinct primes `ℓ`,
  `p`, every compact open `L₀ ≤ GJ(A_f^{ℓp})` contains a compact open level
  `K^{ℓ,p}` with `HarrisSufficientlySmall`. Finiteness of `A` over `ℚ` is
  `Module.Finite.trans E A`, and positivity is
  `isPositive_of_hasDefiniteSignature` from `DefinitePositivity`.

## Scope

- **Signature input.** The definite group is given by the published
  `HasDefiniteSignature`; its relation to compactness of the real unitary
  group is not formalized.
- **Nonzero algebra.** `A ≠ 0` is assumed (automatic for Harris's central
  simple algebra; not derived here).
- **Adelic setting.** As in `HarrisDividingLevelFree`, Harris's
  `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}` is read as `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`.

## Provenance

The source is Harris (1999), Sections 1 and 4, printed pp. 301 and 310, read
in the original (rendered pages). The predicate `HarrisSufficientlySmall`
packages Harris's requirement; the monotonicity and the combination of
`HarrisSmallLevels` with `DefinitePositivity` are written for this module.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- `Langlands.Shimura.Unitary.HarrisSmallLevels`
  (`exists_harrisDividingLevelFree`), from candidate
  `b5ac1f92-254f-4424-a40e-6b67a1e352b7`, which depends on candidates
  `7c0a7e9b-59ea-41f0-bed4-cd80fcd887f6`,
  `86a1bf69-cdc3-42a2-80dd-390814d5926d` and
  `c19177f9-ea37-49e0-9b3f-81e8966cb1f4`;
- `Langlands.Shimura.Unitary.DefinitePositivity`
  (`SecondKindInvolution.isPositive_of_hasDefiniteSignature`), from
  candidate `851f3621-484e-497e-9d1c-57aaf72048f9`;
- the published `Langlands.Shimura.Unitary.HarrisDividingLevelFree`
  (`DividingLevelFree`, `HarrisDividingLevelFree`, `splitLevel_mono`),
  `HarrisPairPoints` (`ellPlace`, `primePlace`), `Signature`
  (`HasDefiniteSignature`) and `CMData` (`rationalInvolution`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
  particular `DoubleCoset.eq` and `Module.Finite.trans`.
