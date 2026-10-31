# Matched expansion of two-block induced zeta integrals and their transforms

Module `Langlands.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion`.
Author: Worker 33.

This module proves the internal interface `TwoBlockMatchedZetaExpansionStatement`
(defined in `TwoBlockFunctionalEquationAssembly`). It is the two-block form of the
coefficient computation in the proof of Godement–Jacquet 1972, Theorem 3.4 (printed
pages 37–42): the original zeta integral of an induced coefficient and the zeta
integral of the Fourier transform of the test against the inverse-transpose
coefficient both become finite sums of products of block zeta integrals, with the
same finite data. The module introduces no definitions.

The route differs from the source in one point. On printed pages 41–42 the source
replaces `Φ` by `Φ̂` and the coefficient `f` by the coefficient `f̌` of the
contragredient, and uses Lemma 3.4.0 (printed 38) to keep the same constants `c_ij`.
The target statement uses the inverse-transpose transform `ι f` instead. Here the
transformed integral is first substituted along `g ↦ ι g = (g⁻¹)ᵀ`, which preserves
the normalized Haar measure. It is then computed with the same compact subgroup `K`,
the same compact coefficient kernel and the same parabolic coordinates as the
original integral. The role of Lemma 3.4.0 is played by the published partial
Fourier identity of `TwoBlockPartialFourier`.

Notation. `F` is a canonical p-adic field with the Borel structures used by
`Padic.matrixIntegral`, `abv` is the canonical normalized absolute value,
`dw g s = determinantWeight abv g s = |det g|^s`, and `Z(Ψ, s, c)` is
`Padic.matrixIntegral F Ψ s c`. The rank is `t + 1 = (m 0 + 1) + (m 1 + 1)`, with
`n₀ = m 0 + 1`, `n₁ = m 1 + 1` and `jpssShift n = n/2`. `F̂` is
`rectangularFourierEquiv ψ ν r r hsd` at the relevant size, for `ν` self-dual for
`ψ`. The two-block parabolic data `parabolicPoint h (L, x) = [[a, a x], [0, d]]`
(`L = (a, d)`), `parabolicMeasure`, `halfModulus = δ_P^(1/2)`, `blockAbs`,
`leviCoefficientWeight`, `radicalWeight` and the published results quoted below
come from `TwoBlockParabolicHaar`, `TwoBlockSchwartz` and `TwoBlockZetaExpansion`.

## Weights

- `dual_weight_identity ht hA hD s`: for real `A, D > 0` and
  `m₀ + 1 + (m₁ + 1) = t + 1`,
  `(A D)^(-(s + t/2)) · (A^(m₁+1) / D^(m₀+1))^(1/2) =
  A^(-(s + m₀/2)) · D^(-(s + m₁/2) - (m₀+1))` as complex powers. Proof: write every
  power as `exp (log · …)`, use `log (A D) = log A + log D` and
  `log √(A^(n₁)/D^(n₀)) = (n₁ log A - n₀ log D)/2`, and compare exponents with
  `t = m₀ + m₁ + 1`.
- `dual_levi_weight_identity F h L x s`:
  `dw (parabolicPoint h (L, x)) (-(s + t/2)) · halfModulus F h L =
  dw a (-(s + m₀/2)) · dw d (-(s + m₁/2) - (m₀+1))`. Proof: `det_parabolicPoint`,
  `halfModulus_eq` and the previous identity with `A = |det a|`, `D = |det d|`.
- `determinantWeight_sub_natCast_mul_pow F g w k`:
  `dw g (w - k) · |det g|^k = dw g w` (`Complex.cpow_natCast`, `Complex.cpow_add`).

## The abstract matched expansion

`exists_matched_zeta_expansion_of_kernel F h ψ ν hsd K hK hPK μK Γ hΓ φ c₀ c₁ hc₀ hc₁
hexp Φ` has the hypotheses of the published `exists_zeta_expansion_of_kernel`, plus
`ψ`, `ν` and `hsd : IsSelfDual ψ ν`:

- `K` is a compact open subgroup of `GL_(t+1)(F)` with `GL_(t+1) = P K`, and `μK` is a
  finite measure on `K` (Borel);
- `Γ : K → GL_(t+1) → ℂ` is jointly continuous, and for all `k, k' ∈ K`, `L`, `x`:
  `Γ k (parabolicPoint h (L, x) * k') = halfModulus L · ∑ j, φ j (k, k') · c₀ j a · c₁ j d`,
  with `φ j` Schwartz–Bruhat on `K × K` and continuous `c₀ j`, `c₁ j`;
- `Φ` is a full-matrix test.

Write `f g = ∫ k, Γ k (k g) dμK`. The conclusion: there are a finite type `ι`, weights
`w`, block tests `Ψ₀ i`, `Ψ₁ i` and indices `jj i` such that

1. for every `s` at which every block test converges against every `c₀ j` at
   `s + m₀/2` and against every `c₁ j` at `s + m₁/2`,
   `Z(Φ, s + t/2, f) = ∑ i, w i · Z(Ψ₀ i, s + m₀/2, c₀ (jj i)) · Z(Ψ₁ i, s + m₁/2, c₁ (jj i))`;
2. for every `s` at which every block test converges against every `ι c₀ j` at
   `s + m₀/2` and against every `ι c₁ j` at `s + m₁/2`,
   `Z(F̂ Φ, s + t/2, ι f) =
   ∑ i, w i · Z(F̂ Ψ₀ i, s + m₀/2, ι c₀ (jj i)) · Z(F̂ Ψ₁ i, s + m₁/2, ι c₁ (jj i))`,

where `ι = coefficientIota`. The data do not depend on `s`.

Proof. The shared data are chosen first.

- The radical measure is `dx = rectangularMeasure ν n₀ n₁` (Haar, since `ν` is
  σ-finite by `selfDualSigmaFinite`), and `ρ = parabolicMeasure F h dx`. On `K` the
  second measure is `ν' = comap val (generalLinearHaar)`, which is finite and maps to
  the Haar measure restricted to `K`.
- `exists_matrixTranslate_expansion` gives `Φ (k⁻¹ X k') = ∑ l, χ l (k, k') Φl l X`
  for `k, k' ∈ K`, with `χ l` Schwartz–Bruhat on `K × K` and
  `Φl l = matrixTranslate Φ …`.
- `exists_upperBlockIntegral_expansion` (with `dx`) gives, for each `l`,
  `∫ B, Φl l [[A, B], [0, D]] dx = ∑ r, Ψ₀ l r A · Ψ₁ l r D`.
- `ι = Σ l, Fin (R l) × Fin N`, `w (l, r, j) = C⁻¹ · W l j`, `Ψ₀ (l, r, j) = Ψ₀ l r`,
  `Ψ₁ (l, r, j) = Ψ₁ l r`, `jj (l, r, j) = j`, where
  `W l j = ∫ χ l · φ j d(μK × ν')` and `C = ρ (parabolicPoint⁻¹ K)`.

Original integral. This part repeats the proof of the published
`exists_zeta_expansion_of_kernel`, with `dx` in place of `Measure.addHaar`. With
`H g = Φ g · dw g (s + t/2)`, `Q (l, j) z = Φl l (parabolicPoint z) · leviCoefficientWeight`,
and `ψ (l, j) k k' = χ l (k, k') φ j (k, k')`, the integrand expands as
`H (k⁻¹ p k') Γ k (p k') = ∑ ψ (l, j) k k' Q (l, j) z` for `p = parabolicPoint z`.
`CompactFactorization.integrable_integral_coefficient_of_expansion` gives
`Z(Φ, s + t/2, f) = C⁻¹ ∑ W l j ∫ Q (l, j) dρ`. The published parabolic reduction
`integral_testFunction_parabolicPoint` and `integral_leviCoefficientWeight` turn each
`∫ Q (l, j) dρ` into `∑ r, Z(Ψ₀ l r, s + m₀/2, c₀ j) Z(Ψ₁ l r, s + m₁/2, c₁ j)`.

Transformed integral.

- `matrixIntegral_coefficientIota` with
  `Padic.generalLinearHaar_measurePreserving_inverseTranspose` rewrites
  `Z(F̂ Φ, s + t/2, ι f)` as `∫ H' g f g`, with `H' g = F̂ Φ (ι g) · dw g (-(s + t/2))`.
- For `k, k' ∈ K`, `Padic.rectangularFourierEquiv_inverseTranspose_translate_of_mem`
  applied to the same expansion of `Φ (k⁻¹ X k')` gives
  `F̂ Φ (ι (k⁻¹ p k')) = ∑ l, χ l (k, k') F̂ (Φl l) (ι p)`, with the same `χ l`. The
  weight `dw` is unchanged by `k⁻¹, k'` (`determinantWeight_mul_of_mem`), and
  `dual_levi_weight_identity` splits `dw p (-(s + t/2)) · halfModulus L`. Hence
  `H' (k⁻¹ p k') Γ k (p k') = ∑ ψ (l, j) k k' Q' (l, j) z` with the same `ψ` and
  `Q' (l, j) (L, x) = F̂ (Φl l) (ι (parabolicPoint (L, x))) · u₀ j a · u₁ j d`, where
  `u₀ j a = c₀ j a · dw a (-(s + m₀/2))` and
  `u₁ j d = c₁ j d · dw d (-(s + m₁/2) - n₀)`.
- `integrable_integral_coefficient_of_expansion`, with the same `ρ`, `μK`, `ν'` and
  `ψ`, gives `Z(F̂ Φ, s + t/2, ι f) = C⁻¹ ∑ W l j ∫ Q' (l, j) dρ`, with the same
  constants `C` and `W l j`.
- `Padic.integrable_integral_dualParabolic_levi` (with `g = parabolicPoint h`,
  `e = blockEquiv h`, `μ i = generalLinearHaar F (m i)`, so that the measure is `ρ`)
  computes `∫ Q' (l, j) dρ`. Its hypothesis `hpart` is
  `integral_rectangularFourierIntegral_blockMatrix_lowerLeft_of_tensor` applied to
  `Φl l` and the upper-block expansion above: the lower-left integral of `F̂ (Φl l)`
  is `∑ r, F̂ (Ψ₀ l r) · F̂ (Ψ₁ l r)`. Its integrability hypotheses for `u₀ j` and
  `u₁ j · |det d|^(n₀)` are the assumed convergence of the block tests against
  `ι c₀ j` and `ι c₁ j`, via `matrixConverges_coefficientIota_iff` and
  `determinantWeight_sub_natCast_mul_pow`. By `matrixIntegral_coefficientIota` on
  the blocks, the result is
  `∫ Q' (l, j) dρ = ∑ r, Z(F̂ Ψ₀ l r, s + m₀/2, ι c₀ j) Z(F̂ Ψ₁ l r, s + m₁/2, ι c₁ j)`.

Both identities are then regrouped over `ι` with `Fintype.sum_sigma` and
`Fintype.sum_prod_type`.

## The forward form and the interface

- `exists_twoBlock_matched_zeta_expansion F h σ hσs hσa ψ ν hsd Φ ℓ v`: for smooth
  admissible blocks `σ`, `ℓ : SmoothDual I` and `v : smoothVectors I` of
  `I = F.canonicalNormalizedProductInduced (succBlockShape m h) σ`, there are a finite
  type `ι`, weights `w`, block tests `Ψ₀`, `Ψ₁` and actual block bi-smooth
  coefficients `f₀ i ∈ biSmoothMatrixCoefficients (σ 0)`,
  `f₁ i ∈ biSmoothMatrixCoefficients (σ 1)`, such that the two identities above hold
  for `f = biSmoothCoefficient I ℓ v`. The first holds whenever every block test
  converges against every bi-smooth coefficient of `σ 0` at `s + m₀/2` and of `σ 1` at
  `s + m₁/2`; the second whenever the same holds for their `ι`-transforms. The kernel
  data are those of the published `exists_twoBlock_zeta_expansion`:
  `exists_compactProductCoefficientFormula` writes `f g = ∫ k, Γ k (k g) dμK` with the
  compact coefficient kernel `Γ`, and `exists_compactProductPairing_expansion` together
  with `normalizedProductInduced_covariant` gives the hypothesis `hexp` with block
  matrix coefficients `c₀ j`, `c₁ j`. These lie in `biSmoothMatrixCoefficients` because
  the blocks are smooth.
- `padic_matrixIntegral_smul`: `Z(Ψ, s, c • f) = c · Z(Ψ, s, f)` (`matrixIntegral_smul`).
- `Langlands.GodementJacquet.twoBlockMatchedZetaExpansion :
  TwoBlockMatchedZetaExpansionStatement.{uF,uV}`. Proof: apply the forward form.
  Reindex `ι` by `Fintype.equivFin`. Absorb the weight into the first coefficient,
  `f0 i = w i • f₀ i`, using `padic_matrixIntegral_smul` and
  `coefficientIota (w • c) = w • coefficientIota c` (definitional). The half-planes
  are `max a₀ a₁` and `max b₀ b₁`, where `a i` comes from the block convergence
  assertion `(hdata i).1.1` (`MatrixConvergesOnRight` of `σ i`) and `b i` from
  `(hdata i).2.1.1` (`IotaMatrixConvergesOnRight` of `σ i`).

Compiled with 0 errors and 0 warnings. Axioms of `twoBlockMatchedZetaExpansion`:
`propext`, `Classical.choice`, `Quot.sound`.
