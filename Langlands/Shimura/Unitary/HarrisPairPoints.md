# The points at two distinct primes

Author: Worker 19.

Harris's hypothesis (4.5) concerns the group `K_ℓ × C_p` inside
`GJ_ℓ × GJ_p`, for distinct primes `ℓ` and `p`. The companion module
`HarrisDividingLevelFree` works with the published splitting at the places
dividing `n = ℓ p`, so `K_ℓ × C_p` appears there as a subgroup
`pairLevel K_ℓ C_p` of `σ(∏_{v ∣ ℓ p} ℚ_v)`. This module proves that
`σ(∏_{v ∣ ℓ p} ℚ_v)` is `σ(ℚ_ℓ) × σ(ℚ_p)`, and that `pairLevel K_ℓ C_p`
is `K_ℓ × C_p` under this identification.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "(4.5) `K_ℓ × C_p`
acts without fixed points on `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`". Here `K_ℓ` is
a subgroup of `GJ_ℓ` and `C_p` of `GJ_p`, with `ℓ ≠ p`.

## Declarations

All declarations are in namespace `Langlands.Shimura.DefiniteForms`.

### Places of `ℚ` dividing `ℓ p`

Let `ℓ` and `p` be distinct primes, `vℓ` a finite place of `ℚ` whose prime
ideal contains `ℓ`, and `vp` one whose prime ideal contains `p`.

- `natCast_mul_mem_asIdeal_iff`: a finite place contains `ℓ p` if and only
  if it contains `ℓ` or `p`, since its ideal is prime.
- `not_natCast_mem_and_natCast_mem`: no finite place contains both `ℓ` and
  `p`. They are coprime, so `1 = a ℓ + b p` would lie in the ideal.
- `ellPlace p vℓ` and `primePlace ℓ vp` are `vℓ` and `vp` as places
  dividing `ℓ p` (through `dividingPlaceOfDvd` of `HarrisDividingLevelFree`).
- `ellPlaceUnique` and `primePlaceUnique` (`Unique` instances, as
  abbreviations): among the places dividing `ℓ p`, `vℓ` is the only one
  containing `ℓ`, and `vp` is the only one not containing `ℓ`. They use
  the published `existsUnique_finitePlace_natCast_mem`.
- `pairCompletionEquiv hℓ hp hℓp vℓ vp` is the continuous `ℚ`-algebra
  isomorphism `∏_{v ∣ ℓ p} ℚ_v ≃ ℚ_ℓ × ℚ_p`, `x ↦ (x_{vℓ}, x_{vp})`
  (`pairCompletionEquiv_apply`). It splits the index set by whether the
  place contains `ℓ` (Mathlib's `RingEquiv.piEquivPiSubtypeProd`), and each
  part has one element (`RingEquiv.piUnique`). Continuity of the inverse
  comes from the matching homeomorphisms. The construction follows the
  published `dividingCompletionEquiv` for one prime.

### Points

Let `σ : AlgebraInvolution ℚ A` with `A` finite over `ℚ`.

- `pairPointsEquiv σ hℓ hp hℓp vℓ vp` is the isomorphism of topological
  groups `σ(∏_{v ∣ ℓ p} ℚ_v) ≃ₜ* σ(ℚ_ℓ) × σ(ℚ_p)`. It is the published
  `pointsContinuousEquiv` of `pairCompletionEquiv`, followed by the
  published `prodPointsContinuousEquiv`.
- `pairPointsEquiv_apply`: its components are the published local maps
  `dividingLocalMap` at `vℓ` and at `vp`.
- `pairLevel_eq_comap`: `pairLevel K_ℓ C_p` (at `ellPlace` and
  `primePlace`) is the inverse image of `K_ℓ × C_p` under
  `pairPointsEquiv`.
- `harrisDividingLevelFree_iff`: Harris's (4.5) in the form
  `HarrisDividingLevelFree` holds if and only if `DividingLevelFree` holds
  for the inverse image of `K_ℓ × C_p` under `pairPointsEquiv`.

## Scope

- The module identifies the groups only. It adds no hypothesis on `K_ℓ`,
  `C_p` or `K^{ℓ,p}`.
- The places `vℓ` and `vp` are inputs. They are unique, by the published
  `existsUnique_finitePlace_natCast_mem`.

## Provenance

Derived from Harris (1999), Section 4, printed p. 310, read in the original:
`K_ℓ × C_p` is a subgroup of `GJ_ℓ × GJ_p`. The identification of the
points at the places dividing `ℓ p` with the product of the points at `ℓ`
and at `p` is an internal construction. It is built from the published
`pointsContinuousEquiv`, `prodPointsContinuousEquiv` and
`existsUnique_finitePlace_natCast_mem` and from Mathlib.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- the companion module `Langlands.Shimura.Unitary.HarrisDividingLevelFree`
  (same candidate: `dividingPlaceOfDvd`, `pairLevel`, `mem_pairLevel`,
  `DividingLevelFree`, `HarrisDividingLevelFree`);
- the published `Langlands.Shimura.Unitary.PointsSplit`
  (`pointsContinuousEquiv`, `prodPointsContinuousEquiv`, `pointsMap_apply_apply`,
  `DividingPoints`, `dividingLocalMap`);
- the published `Langlands.Global.PrimeToFiniteAdeles`
  (`existsUnique_finitePlace_natCast_mem`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include `RingEquiv.piEquivPiSubtypeProd`,
`RingEquiv.piUnique`, `Homeomorph.piEquivPiSubtypeProd`,
`Homeomorph.piUnique`, `Nat.coprime_primes`, `Nat.isCoprime_iff_coprime`
and `Ideal.IsPrime.mul_mem_iff_mem_or_mem`.
