# Harris's (4.5) for sufficiently small levels of a definite group

Author: Worker 19.

Harris (1999) assumes that the away level `K^{ℓ,p}` is "sufficiently small
so that (4.5)" holds. This module shows that such levels exist below every
compact open level, for a definite group (a positive involution). It
combines two modules. `HarrisLevelFreePositive` (integrated together with
this module) proves (4.5) for compact factors when the away level is
torsion-free at one place. `TorsionFreeLevels`
constructs an open subgroup of `σ(ℚ_v)` without nontrivial elements of
finite order, for `v` over a prime `q ≥ 3`.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "We strengthen (3.6)
by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is
sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`."

Harris and Taylor (2001), Chapter III, Section 1, printed p. 90 (PDF p. 98):
"By sufficiently small we shall mean that the projection of `U` to `G(ℚ_x)`
for some prime `x` contains no element of finite order other than 1."

## Setting

Declarations are in namespace `Langlands.Shimura.DefiniteForms`.

- `σ : AlgebraInvolution ℚ A`, with `A` finite over `ℚ`. `σ(A_f^n)` is the
  published `σ.PrimeToPoints n`, and `primeToLocalMap σ n v` is its component
  at a place `v` not dividing `n` (from `HarrisLevelFreeSmall`).
- `SmallLevels.congruenceLevel σ v q` is the principal congruence level
  modulo `q` of `σ(ℚ_v)`, from `TorsionFreeLevels`.
- `splitLevel`, `pairLevel`, `HarrisDividingLevelFree`, `ellPlace` and
  `primePlace` are as in the published `HarrisDividingLevelFree` and
  `HarrisPairPoints`.

## Declarations

- `continuous_primeToLocalMap`: the component at `v` is continuous on
  `σ(A_f^n)`. It is the published `continuous_pointsMap` applied to the
  evaluation of the restricted product at `v`.
- `smallAwayLevel σ n v q L₀`: the elements of `L₀ ≤ σ(A_f^n)` whose
  component at `v` lies in `SmallLevels.congruenceLevel σ v q`.
- `smallAwayLevel_le`: it lies in `L₀`.
- `isOpen_smallAwayLevel`: for `q ≠ 0` it is open when `L₀` is, as the
  intersection of `L₀` with the preimage of an open subgroup.
- `isCompact_smallAwayLevel`: for `q ≠ 0` it is compact when `L₀` is. The
  preimage of the congruence level is an open subgroup, hence closed, and a
  closed subset of a compact set is compact.
- `levelTorsionFreeAt_smallAwayLevel`: for `A ≠ 0` and a prime `q ≥ 3`
  contained in `v`, `e⁻¹ (1 × smallAwayLevel)` satisfies
  `LevelTorsionFreeAt` at `v`. This is `levelTorsionFreeAt_splitLevel` with
  `SmallLevels.congruenceLevel_torsionFree`.
- `awayPlace`: a place over a prime `q` different from the primes `ℓ` and
  `p`, viewed as a place not dividing `ℓ p`. It uses the published
  `natCast_mul_mem_asIdeal_iff` and `not_natCast_mem_and_natCast_mem`.
- `HarrisDividingLevelFree.of_smallAwayLevel`: let `ℓ ≠ p` be primes, `v` a
  place over a prime `q ≥ 3` with `q ≠ ℓ, p`, `σ ⊗ ℝ` positive and `A ≠ 0`.
  For compact `K_ℓ`, `C_p` and `L₀`, Harris's (4.5) holds for
  `K^{ℓ,p} = smallAwayLevel σ (ℓ p) v q L₀`. This is
  `HarrisDividingLevelFree.of_isPositive` with the two previous lemmas.
- `exists_harrisDividingLevelFree`: **sufficiently small levels exist.** For
  `σ ⊗ ℝ` positive, `A ≠ 0` and primes `ℓ ≠ p`, every compact open
  `L₀ ≤ σ(A_f^{ℓp})` contains a compact open `L` such that (4.5) holds for
  `L` and every pair of compact `K_ℓ` and `C_p`. The proof takes a prime
  `q > ℓ + p + 2` (Mathlib's `Nat.exists_infinite_primes`), the place of `ℚ`
  over it (the published `existsUnique_finitePlace_natCast_mem`), and
  `L = smallAwayLevel σ (ℓ p) v q L₀`.

## Scope

- **Positivity is a hypothesis.** As in `HarrisLevelFreePositive`, the
  positivity of `σ ⊗ ℝ` is assumed, not derived from `J_∞ ≅ ∏ U(n)`.
- **Smallness at one place only.** The constructed level is small at the
  single place `v`; nothing else about the shape of `L` is claimed. In
  particular `L` need not be a product of local factors.
- **Adelic setting.** As in `HarrisDividingLevelFree`, Harris's
  `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}` is read as `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`.

## Provenance

The sources are Harris (1999), printed p. 310, and Harris and Taylor
(2001), printed p. 90, read in the original. They state the smallness
condition but do not construct small levels. This module only assembles
results of `HarrisLevelFreePositive` and `TorsionFreeLevels`; the assembly
and the choice of an auxiliary prime `q` are written for this module.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`:
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Formal dependencies:

- `Langlands.Shimura.Unitary.HarrisLevelFreePositive`
  (`levelTorsionFreeAt_splitLevel`, `HarrisDividingLevelFree.of_isPositive`),
  integrated together with this module (same candidate). It depends on
  candidates `7c0a7e9b-59ea-41f0-bed4-cd80fcd887f6` (`HarrisLevelFreeSmall`:
  `primeToLocalMap`, `LevelTorsionFreeAt`) and
  `86a1bf69-cdc3-42a2-80dd-390814d5926d` (`PositiveArithmeticFinite`);
- `Langlands.Shimura.Unitary.TorsionFreeLevels`
  (`SmallLevels.congruenceLevel`, `SmallLevels.isOpen_congruenceLevel`,
  `SmallLevels.congruenceLevel_torsionFree`), from candidate
  `c19177f9-ea37-49e0-9b3f-81e8966cb1f4`;
- the published `Langlands.Shimura.Unitary.Adelic` (`continuous_pointsMap`),
  `Langlands.Shimura.Unitary.HarrisPairPoints`
  (`natCast_mul_mem_asIdeal_iff`, `not_natCast_mem_and_natCast_mem`) and
  `Langlands.Global.PrimeToFiniteAdeles`
  (`existsUnique_finitePlace_natCast_mem`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
  particular `RestrictedProduct.continuous_eval`,
  `Subgroup.isClosed_of_isOpen`, `IsCompact.inter_right` and
  `Nat.exists_infinite_primes`.
