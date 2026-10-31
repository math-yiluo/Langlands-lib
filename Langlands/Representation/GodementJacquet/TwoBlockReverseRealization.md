# Reverse realization of products of block zeta integrals

Module `Langlands.Representation.GodementJacquet.TwoBlockReverseRealization`.
Author: Worker 1112.

This module proves the reverse inclusion of Godement–Jacquet, *Zeta Functions of
Simple Algebras* (1972), Theorem 3.4 (printed 43–45) for two blocks: every product
of rational values of individual block zeta integrals lies in the Laurent span of
the values of the normalized induced representation. Instead of the source's
Lemma 3.4.6 (a duality argument), the implemented proof realizes each product
directly with sections supported on one double coset `P K₀`. It also packages, with
the forward module `TwoBlockZetaExpansion`, all three components of Worker 704's
`TwoBlockMatrixGeneratorInputs`.

Notation as in `TwoBlockZetaExpansion`; `P` is the upper two-block parabolic,
`parabolicPoint (L, x) = [[a, a x], [0, d]]`.

## Sets and test functions

- `parabolicCompactSet F h K₀ = {q l | q ∈ P, l ∈ K₀}` (definition), open
  (`isOpen_parabolicCompactSet`, a union of left translates of `K₀`).
- `integralBox F r s` (definition): matrices with all entries in the integer ring
  `F.canonicalTopologicalData.Integers`; compact, open and containing `0`.
  `integralBoxTest F r s` is its indicator, a Schwartz–Bruhat function with
  `integralBoxTest_zero : integralBoxTest 0 = 1`.
- `blockSplit` / `blockJoin` (definitions) pass between a matrix and its four blocks
  `((A, D), B), C` in the block convention `blockEquiv h`;
  `blockJoin_blockSplit`, `blockSplit_upper`, and continuity.
- `reverseTest F h Φ₀ Φ₁` (definition): `X ↦ Φ₀(A) Φ₁(D) 1_box(B) 1_box(C)` for the
  blocks `[[A, B], [C, D]]` of `X` (via `SchwartzBruhat.compLeftInverse`).
  `reverseTest_upper` evaluates it on `[[A, B], [0, D]]`, and
  `upperBlockIntegral_reverseTest`: its upper-block integral is
  `dx(box) · Φ₀(A) Φ₁(D)`.

## Compact subgroups

- `exists_compactOpen_biInvariant`: every full-matrix test is invariant on both
  sides under some compact open subgroup contained in a prescribed open subgroup
  (from `eventually_matrixTranslate_eq` and `compactOpenSubgroupBasis`).
- `leviModulus_eq_one_of_mem`: `δ_P(q) = 1` for `q ∈ P` in a compact subgroup
  (the continuous character `leviModulus ∘ leviProjection` is trivial on the compact
  subgroup `P ∩ K`, by `eq_one_of_isCompact`).

## The kernel computation

`reverse_zeta_of_kernel`: let `K₀` be a compact open subgroup, `ν` a finite Borel
measure on an open subgroup `K`, `Γ : K → GL_(t+1) → ℂ` jointly continuous and
`Γ₀ : GL_(t+1) → ℂ` continuous, with:
`Γ k = 0` for `k ∉ P K₀`; `Γ k y = Γ₀ (q⁻¹ y)` whenever `k = q l`, `q ∈ P`, `l ∈ K₀`;
`Γ₀ = 0` off `P K₀`; and
`Γ₀ (parabolicPoint (L, x) l) = δ_P(L)^(1/2) c₀(a) c₁(d)` for `l ∈ K₀`, with continuous
`c₀, c₁`. Let `Φ` be invariant on both sides under `K₀`, and `s` such that all
block tests converge against `c₀` at `s + m₀/2` and against `c₁` at `s + m₁/2`. Then
the coefficient `g ↦ ∫ k, Γ k (k g) dν` has convergent zeta integral at `s + t/2`, and
it equals
`ν(K ∩ P K₀) · (dL × dx)(parabolicPoint ⁻¹' K₀)⁻¹ · μ(K₀) · ∫ Φ^P(a, d) · leviCoefficientWeight · |det a|^(-n₁)`,
with `dx = Measure.addHaar`.

Proof. With `H g = Φ g |det g|^(s + t/2)` and `Ψ₀ = H Γ₀`:
1. For `k = q l ∈ P K₀`, left `K₀`-invariance of `H` gives
   `H (k⁻¹ y) Γ k y = Ψ₀ (q⁻¹ y)`, and the expression vanishes for `k ∉ P K₀`;
   `CompactFactorization.integrable_integral_coefficient_of_translate` then gives
   integrability and the value `ν(K ∩ P K₀) ∫ Ψ₀`.
2. `Ψ₀` is supported on `P K₀`. For `l ∈ K₀`, right `K₀`-invariance gives
   `Ψ₀ (parabolicPoint z l) = Φ(parabolicPoint z) · leviCoefficientWeight(z.1)`, an
   integrable function of `z` by the parabolic reduction
   (`integral_testFunction_parabolicPoint`, with hypothesis from
   `integrable_leviCoefficientWeight`). The factorization over `K₀` for functions
   supported on `P K₀` (`integrable_comp_mul_iff_of_subset`,
   `integral_restrict_integral_mul_of_subset`) gives integrability of `Ψ₀` and
   `∫ Ψ₀ = (dL × dx)(parabolicPoint ⁻¹' K₀)⁻¹ μ(K₀) ∫ Φ^P · weight`.

## The representation-theoretic realization

`exists_twoBlock_reverse_realization F h σ hσs hσa Φ₀ ℓ₀ v₀ Φ₁ ℓ₁ v₁`: for smooth
admissible blocks there are `Φ`, `ℓ`, `v` (an actual smooth functional and smooth
vector of `π = F.canonicalNormalizedProductInduced (succBlockShape m h) σ`) and
`κ ≠ 0` such that, whenever the block integrals with `biSmoothCoefficient (σ i) ℓᵢ vᵢ`
converge at the block shifts for all block tests,
`Padic.MatrixConverges F Φ (s + t/2) (biSmoothCoefficient π ℓ v)` and
`Padic.matrixIntegral F Φ (s + t/2) (biSmoothCoefficient π ℓ v) =
 κ · Z₀(Φ₀, s + m₀/2) · Z₁(Φ₁, s + m₁/2)`.

Construction. Worker 704's `exists_compactProductCoefficientFormula` gives `K`, a Haar
probability `μK` and the equivalence `E`. Take `Φ = reverseTest Φ₀ Φ₁`; choose compact
open `K₀ ≤ K` fixing `Φ` on both sides and such that `P ∩ K₀` fixes the pure tensor
`w = v₀ ⊗ v₁` and the pure functional
`λ = smoothDualTensorMap σ (ℓ₀ ⊗ ℓ₁)` in the twisted actions of the two inductions
(`exists_twist_comp_fixed`, `exists_compact_conj_fixed`, using smoothness of the
external tensor and of the smooth contragredient). Let `f` and `h'` be the compact
double-coset sections on `P · 1 · K₀` with values `w` and `λ`
(`compactDoubleCosetSection`), `v = f`, and `ℓ = E.symm h'`. Then
`biSmoothCoefficient π ℓ v g = ∫ k, ⟨h'(k), f(k g)⟩ dμK`. The hypotheses of
`reverse_zeta_of_kernel` hold with `Γ k y = ⟨h'(k), f(y)⟩` and `Γ₀ y = ⟨λ, f(y)⟩`:
the support statements follow from `compactDoubleCosetSection_mem_of_ne_zero`; for
`k = q l` one has `h'(k) = δ^(1/2)(q) σ^∨(q) λ` with `δ(q) = 1` (as `q ∈ K`), so
`⟨h'(k), f(y)⟩ = ⟨λ, σ(q)⁻¹ f(y)⟩ = ⟨λ, f(q⁻¹ y)⟩` by the covariance
`normalizedProductInduced_covariant`; and
`⟨λ, f(parabolicPoint (L, x) l)⟩ = δ^(1/2)(L) ⟨λ, σ(L) w⟩ = δ^(1/2)(L) c₀(a) c₁(d)`
(`matrixCoefficient_smoothDualTensorMap_tprod`). Finally
`Φ^P = dx(box) Φ₀ ⊗ Φ₁` and `integral_leviCoefficientWeight` give the product, with
`κ = ν(K ∩ P K₀) (dL × dx)(parabolicPoint ⁻¹' K₀)⁻¹ μ(K₀) dx(box)`, which is nonzero
because each factor is the measure of a nonempty open set of finite measure.
`twoFamily` (definition) builds the dependent pair families on `Fin 2`.
This theorem is compiled with `set_option maxHeartbeats 1600000` (a finite limit).

## Generator inputs

- `twoBlock_reverse_generatorInput F h σ hσs hσa P hblock`: if both blocks satisfy
  `Padic.MatrixAnalyticAssertions F (σ i) (P i)`, then for block tests, actual block
  bi-smooth coefficients and their actual shifted rational values `R`, `S`,
  `R * S ∈ zetaSpan (matrixRationalValues … (generalLinearHaar F.Carrier t) π)`.
  Proof: with the realization, `C(κ) (R S)` is an actual shifted rational value of
  `π` (continuations multiply, `hasRationalContinuation_const_mul`, agreement on the
  right half-plane where block convergence holds), hence lies in the span; multiply
  by `C(κ⁻¹)`.
- `twoBlock_matrixGeneratorInputs F h σ hσs hσa P hblock`: the complete
  `TwoBlockMatrixGeneratorInputs q abv (generalLinearHaar F.Carrier t) π m
  (fun i => generalLinearHaar F.Carrier (m i)) σ` with canonical `q` and `abv`, from
  `twoBlock_forward_generatorInputs` and the reverse input.

## Scope

The blocks need only be smooth and admissible and satisfy the matrix analytic
assertions; no irreducibility, central-character or functional-equation hypothesis
is used. Assembly of the full analytic assertions from these inputs is Worker 704's
`matrixAnalyticAssertions_twoBlock_of_generators`.
