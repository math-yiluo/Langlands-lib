# Harris's (4.5) for sufficiently small levels

Author: Worker 19.

Harris (1999) takes the away level `K^{ℓ,p}` "sufficiently small so that"
his hypothesis (4.5) holds. This module proves (4.5) from two explicit
conditions:

- `RationalFiniteOrder`: every rational point whose diagonal image lies in
  a conjugate of the level has finite order;
- `LevelTorsionFreeAt`: at one place `v` not dividing `ℓ p`, the away level
  has no nontrivial local elements of finite order.

The second condition is the kind of smallness Harris means. The first is a
property of the definite group `GJ`, which this module assumes and does not
prove.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "We strengthen (3.6)
by assuming that `K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is
sufficiently small so that (4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`."

Harris does not say which smallness he uses. The condition
`LevelTorsionFreeAt` is the analog, for the group `GJ(A_f)` itself, of the
published `LevelSmallAt` of Worker 57
(`Langlands.Shimura.Unitary.SufficientlySmallLevels`). That predicate follows
Harris and Taylor (2001), Chapter III, Section 1, printed p. 90: every
finite-order element of the local image of the level is the identity.
`LevelSmallAt` is stated for the opposite group used in the normalized CM
polarized tower, so it is not reused here.

## Setting

Declarations are in namespace `Langlands.Shimura.DefiniteForms`, except
`diagonalPoints_injective` (namespace `Langlands.Shimura.AlgebraInvolution`).

- `σ : AlgebraInvolution ℚ A`, with `A` finite over `ℚ`. `GJ(ℚ)` is the
  published `σ.similitudes` and `GJ(A_f)` the published
  `σ.FiniteAdelicPoints`. `σ.finiteAdelicDiagonal` is the diagonal map and
  `σ.finiteLocalMap v` the published component at a finite place `v`.
- `n ≠ 0` and `e = σ.finiteAdelicPointsSplit n hn` is the published
  splitting `σ(A_f) ≃ₜ* σ(∏_{v ∣ n} ℚ_v) × σ(A_f^n)`. `splitLevel σ n hn U L`
  is the level `e⁻¹ (U × L)` and `DividingLevelFree` is Harris's (4.5), both
  from `HarrisDividingLevelFree`.

## Declarations

### Local components

- `AlgebraInvolution.diagonalPoints_injective`: the diagonal map
  `σ.similitudes → σ.Points S` is injective for every nontrivial
  `ℚ`-algebra `S`. Both components are injective: `A → S ⊗ A` because `A` is
  flat over `ℚ`, and `ℚ → S` because `ℚ` is a field.
- `primeToEvaluation n v` is evaluation of the published prime-to-`n`
  finite adeles at a place `v` not dividing `n`. `primeToLocalMap σ n v` is
  the induced map `σ(A_f^n) →* σ(ℚ_v)`.
- `primeToLocalMap_finiteAdelicPointsSplit`: at such a place, the component
  of `g` is the component of its prime-to-`n` part `(e g).2`.
- `finiteLocalMap_factorHom`: the published embedding `factorHom e` of the
  first factor has trivial component at every place not dividing `n`.

### The two conditions

- `LevelTorsionFreeAt σ v K : Prop`: for every `k ∈ K`, if
  `σ.finiteLocalMap v k` has finite order then it is `1`.
- `RationalFiniteOrder σ K : Prop`: for every `g ∈ GJ(A_f)` and `γ ∈ GJ(ℚ)`,
  if `g⁻¹ γ g ∈ K` then `γ` has finite order.
- `LevelTorsionFreeAt.mono` and `RationalFiniteOrder.mono`: both pass to
  smaller levels.

### (4.5)

- `DividingLevelFree.of_levelTorsionFreeAt`: let `v` be a place not dividing
  `n`. Suppose `RationalFiniteOrder` holds for `e⁻¹ (U × L)` and
  `LevelTorsionFreeAt` at `v` holds for `e⁻¹ (1 × L)`. Then `U` acts without
  fixed points on `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`.
  - Proof: suppose `g u` and `g` have the same class, with `u ∈ U` embedded
    as `f = factorHom e u`. Then `g = γ g f k` with `γ` rational and `k` in
    `e⁻¹ (1 × L)`, so `g⁻¹ γ g = k⁻¹ f⁻¹` lies in `e⁻¹ (U × L)`. Hence `γ` has
    finite order. At `v` the component of `f` is trivial, so the component
    of `k⁻¹` is conjugate to that of `γ` and has finite order. By
    `LevelTorsionFreeAt` it is trivial. Then `γ` is trivial at `v`, and
    `γ = 1` by `diagonalPoints_injective`. Now `f = k⁻¹`; the first
    component of `e k` is trivial, so `u = 1`.
- `HarrisDividingLevelFree.of_levelTorsionFreeAt`: Harris's case. For
  `n = ℓ p`, places `vℓ`, `vp` dividing `ℓ p`, `K_ℓ`, `C_p` and
  `L = K^{ℓ,p}`, if `RationalFiniteOrder` holds for `K^{ℓ,p} × K_ℓ × C_p` and
  `K^{ℓ,p}` is torsion-free at a place `v` containing neither `ℓ` nor `p`,
  then Harris's (4.5) holds. It uses `natCast_mul_mem_asIdeal_iff` from
  `HarrisPairPoints`.

## Scope

- **The finite-order condition is a hypothesis.** For a definite group and
  a compact open level, `GJ(ℚ) ∩ g K g⁻¹` is finite, which gives
  `RationalFiniteOrder`. This module does not prove that; it needs the
  definiteness of `GJ` at the infinite place.
- **Existence of small levels.** The module does not prove that levels
  satisfying `LevelTorsionFreeAt` exist (for instance deep enough
  congruence subgroups at one prime).
- **Adelic setting.** As in `HarrisDividingLevelFree`, Harris's
  `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}` is read as `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`.

## Provenance

The source is Harris (1999), Section 4, printed p. 310, read in the
original (rendered page). The torsion-freeness condition follows the
finite-order condition of Harris and Taylor (2001), printed p. 90, as
formalized in the published `SufficientlySmallLevels`. The decomposition
into the two conditions and the proof are written for this module.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`:
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Formal dependencies:

- the published `Langlands.Shimura.Unitary.HarrisDividingLevelFree`
  (`splitLevel`, `pairLevel`, `DividingLevelFree`,
  `HarrisDividingLevelFree`, `factorHom_mem_splitLevel`, `splitLevel_mono`)
  and `Langlands.Shimura.Unitary.HarrisPairPoints`
  (`natCast_mul_mem_asIdeal_iff`);
- the published `Langlands.Shimura.Unitary.Adelic` (`diagonalPoints`,
  `finiteAdelicDiagonal`, `finiteEvaluation`, `finiteLocalMap`,
  `finiteLocalMap_diagonal`), `Langlands.Shimura.Unitary.PointsSplit`
  (`finiteAdelicPointsSplit`, `finiteAdelicPointsSplit_apply_snd`,
  `pointsMap_apply_apply`), `Langlands.Global.PrimeToFiniteAdeles`
  (`PrimeToFinitePlace`, `PrimeToFiniteAdeles`, `primeToFiniteRestriction`)
  and `Langlands.Shimura.SplitLevelTower` (`factorHom`, `factorHom_apply`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include
`Algebra.TensorProduct.includeRight_injective`, `DoubleCoset.eq`,
`MonoidHom.isOfFinOrder`, `isOfFinOrder_inv_iff` and `MulAut.conj`.
