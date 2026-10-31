import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

noncomputable section

namespace Langlands.RankinSelberg.RankOneGammaTwist

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

section ScalarIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  [MeasurableSpace F] [MeasurableSpace (LeftUnipotentQuotient 0 F)]

/-- Pointwise scalar comparison descends through both total integrals. -/
theorem unequal_integral_scale {r : ℕ} (j k : ℕ) (hr : r = 0 + (j + k + 1))
    (μ : Measure (LeftUnipotentQuotient 0 F))
    (ν : Measure (Matrix (Fin j) (Fin 1) F))
    (W₁ W₂ : WhittakerFunctions ψ r) (W₁' W₂' : InverseWhittakerFunctions ψ 0)
    (c : ℂ)
    (h : ∀ (g : Langlands.GeneralLinear (r + 1) F)
      (a : Langlands.GeneralLinear 1 F), determinant g = determinant a →
      W₁.val g * W₁'.val a = c * (W₂.val g * W₂'.val a)) :
    unequalRankIntegralAt j k hr ψ abv μ ν W₁ W₁' =
      fun s => c * unequalRankIntegralAt j k hr ψ abv μ ν W₂ W₂' s := by
  subst r
  funext s
  change (∫ q, ∫ x, unequalRankIntegrand ψ abv j k W₁ W₁' s x q ∂ν ∂μ) =
    c * ∫ q, ∫ x, unequalRankIntegrand ψ abv j k W₂ W₂' s x q ∂ν ∂μ
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  induction q using Quotient.inductionOn with
  | h a =>
    simp only [unequalRankIntegrand_mk]
    rw [h _ _ (determinant_unequalRankMatrix j k a x)]
    ring

omit [MeasurableSpace F] in
/-- Equal-rank scalar comparison keeps the same Schwartz--Bruhat test. -/
theorem equal_integral_scale (μ : Measure (LeftUnipotentQuotient 0 F))
    (W₁ W₂ : WhittakerFunctions ψ 0) (W₁' W₂' : InverseWhittakerFunctions ψ 0)
    (c : ℂ) (h : ∀ g, W₁.val g * W₁'.val g = c * (W₂.val g * W₂'.val g))
    (Φ : SchwartzBruhat (Fin 1 → F)) :
    equalRankIntegral ψ abv μ W₁ W₁' Φ =
      fun s => c * equalRankIntegral ψ abv μ W₂ W₂' Φ s := by
  funext s
  unfold equalRankIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  induction q using Quotient.inductionOn with
  | h a =>
    simp only [equalRankIntegrand_mk]
    rw [h a]
    ring

end ScalarIntegrals

section Products

variable {F : Type uF} [Field F] [TopologicalSpace F]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n π) (ellC : ℂ →ₗ[ℂ] ℂ) (v : V) (z : ℂ)

/-- Forward coefficient products agree whenever the determinants agree. -/
theorem forward_product (g : Langlands.GeneralLinear (n + 1) F)
    (a : Langlands.GeneralLinear 1 F) (hdet : determinant g = determinant a) :
    (modelMap (Langlands.twist (χ.comp determinant) π)
      (candidateFunctional ψ χ π ℓ) v).val.val g *
        (modelMap (rankOneCharacter 1) (testFunctional ψ 1 ellC) z).val.val a =
    (modelMap π ℓ v).val.val g *
      (modelMap (rankOneCharacter χ) (testFunctional ψ χ ellC) z).val.val a := by
  rw [candidate_coefficient, test_coefficient, test_coefficient, hdet]
  simp only [MonoidHom.one_apply, Units.val_one, one_mul]
  ring

variable [IsTopologicalRing F]

/-- The actual translated dual products have the Weyl sign multiplier. -/
theorem unequal_dual_product (hn : 0 < n)
    (g : Langlands.GeneralLinear (n + 1) F) (a : Langlands.GeneralLinear 1 F)
    (hdet : determinant g = determinant a) :
    (translateWhittaker (ψ.scale (-1)) n
      (firstDualFunction ψ n (modelMap (Langlands.twist (χ.comp determinant) π)
        (candidateFunctional ψ χ π ℓ) v).val) (blockWeylAt 0 n hn)).val g *
      (secondDualFunction ψ 0
        (modelMap (rankOneCharacter 1) (testFunctional ψ 1 ellC) z).val).val a =
    (χ (-1) : ℂ) ^ n *
      ((translateWhittaker (ψ.scale (-1)) n
        (firstDualFunction ψ n (modelMap π ℓ v).val) (blockWeylAt 0 n hn)).val g *
        (secondDualFunction ψ 0
          (modelMap (rankOneCharacter χ) (testFunctional ψ χ ellC) z).val).val a) := by
  simp only [translateWhittaker_apply, firstDualFunction_apply, secondDualFunction_apply,
    candidate_coefficient, test_coefficient]
  rw [determinant_dual_argument n hn, weylLong_one, one_mul,
    determinant_inverseTranspose, hdet, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  simp only [MonoidHom.one_apply, Units.val_one, one_mul]
  ring

/-- In rank one the dual products agree, since the long Weyl element is one. -/
theorem equal_dual_product
    {U : Type uV} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Langlands.GeneralLinear 1 F) U)
    (L : glFunctionals ψ 0 ρ) (u : U) (a : Langlands.GeneralLinear 1 F) :
    (firstDualFunction ψ 0 (modelMap (Langlands.twist (χ.comp determinant) ρ)
      (candidateFunctional ψ χ ρ L) u).val).val a *
      (secondDualFunction ψ 0
        (modelMap (rankOneCharacter 1) (testFunctional ψ 1 ellC) z).val).val a =
    (firstDualFunction ψ 0 (modelMap ρ L u).val).val a *
      (secondDualFunction ψ 0
        (modelMap (rankOneCharacter χ) (testFunctional ψ χ ellC) z).val).val a := by
  simp only [firstDualFunction_apply, secondDualFunction_apply]
  exact forward_product ψ χ ρ L ellC u z _ _ rfl

end Products

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient 0 F))
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n π) (ellC : ℂ →ₗ[ℂ] ℂ) (v : V) (z : ℂ)

omit [IsTopologicalRing F] in
/-- Every forward block integral agrees under the twist transport. -/
theorem unequal_forward (j k : ℕ) (hr : n = 0 + (j + k + 1))
    (ν : Measure (Matrix (Fin j) (Fin 1) F)) :
    unequalRankIntegralAt j k hr ψ abv μ ν
      (modelMap (Langlands.twist (χ.comp determinant) π)
        (candidateFunctional ψ χ π ℓ) v).val
      (modelMap (rankOneCharacter 1) (testFunctional ψ 1 ellC) z).val =
    unequalRankIntegralAt j k hr ψ abv μ ν (modelMap π ℓ v).val
      (modelMap (rankOneCharacter χ) (testFunctional ψ χ ellC) z).val := by
  simpa only [one_mul] using unequal_integral_scale ψ abv j k hr μ ν _ _ _ _ 1
    (fun g a hd => by simpa only [one_mul] using forward_product ψ χ π ℓ ellC v z g a hd)

/-- Every actual dual block integral acquires `χ(-1)^n`. -/
theorem unequal_dual (hn : 0 < n) (j k : ℕ) (hr : n = 0 + (j + k + 1))
    (ν : AdditiveHaarMeasure F) :
    dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν
      (Langlands.twist (χ.comp determinant) π) (rankOneCharacter 1)
      (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC)
      (modelMap _ _ v) (modelMap _ _ z) =
    fun s => (χ (-1) : ℂ) ^ n *
      dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν π (rankOneCharacter χ)
        ℓ (testFunctional ψ χ ellC) (modelMap _ _ v) (modelMap _ _ z) s := by
  exact unequal_integral_scale (ψ.scale (-1)) abv k j (by omega) μ
    (rectangularMeasure ν k 1) _ _ _ _ ((χ (-1) : ℂ) ^ n)
    (unequal_dual_product ψ χ π ℓ ellC v z hn)

omit [IsTopologicalRing F] [MeasurableSpace F] in
/-- The rank-one forward integral keeps every test function. -/
theorem equal_forward
    {U : Type uV} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Langlands.GeneralLinear 1 F) U)
    (L : glFunctionals ψ 0 ρ) (u : U) (Φ : SchwartzBruhat (Fin 1 → F)) :
    equalRankModelIntegral ψ abv μ (Langlands.twist (χ.comp determinant) ρ)
      (rankOneCharacter 1) (candidateFunctional ψ χ ρ L) (testFunctional ψ 1 ellC)
      (modelMap _ _ u) (modelMap _ _ z) Φ =
    equalRankModelIntegral ψ abv μ ρ (rankOneCharacter χ) L (testFunctional ψ χ ellC)
      (modelMap _ _ u) (modelMap _ _ z) Φ := by
  funext s
  simpa only [equalRankModelIntegral, one_mul] using congrFun
    (equal_integral_scale ψ abv μ _ _ _ _ 1
      (fun g => by simpa only [one_mul] using forward_product ψ χ ρ L ellC u z g g rfl) Φ) s

omit [MeasurableSpace F] in
/-- The rank-one dual integral keeps the same Fourier partner. -/
theorem equal_dual
    {U : Type uV} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Langlands.GeneralLinear 1 F) U)
    (L : glFunctionals ψ 0 ρ) (u : U) (Φ : SchwartzBruhat (Fin 1 → F)) :
    dualEqualRankModelIntegral ψ abv μ (Langlands.twist (χ.comp determinant) ρ)
      (rankOneCharacter 1) (candidateFunctional ψ χ ρ L) (testFunctional ψ 1 ellC)
      (modelMap _ _ u) (modelMap _ _ z) Φ =
    dualEqualRankModelIntegral ψ abv μ ρ (rankOneCharacter χ) L (testFunctional ψ χ ellC)
      (modelMap _ _ u) (modelMap _ _ z) Φ := by
  simpa only [dualEqualRankModelIntegral, one_mul] using equal_integral_scale (ψ.scale (-1)) abv μ _ _ _ _ 1
    (fun g => by simpa only [one_mul] using equal_dual_product ψ χ ellC z ρ L u g) Φ

end Integrals

end Langlands.RankinSelberg.RankOneGammaTwist
