import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeStatement
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeProof
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.HarmonicAnalysis.RowFourierHaarSurjectivityProof

/-!
# Proof of the equal-rank change of additive character

For `ψ^a(x) = ψ(ax)`, the translated functionals `v ↦ ℓ(π(d_a) v)`,
`u ↦ ℓ'(σ(d_a) u)` and the Haar measure `ν' = κ ν`, `κ² = |a|`, the original
equal-rank integral for `ψ^a` is a fixed nonzero monomial in `q^(-s)` times the
one for `ψ`, with the same test function. The dual integral for `ψ^a` and the
`ψ^a`-Fourier transform `Φ̂_a(y) = κ^n Φ̂(a y)` is a fixed nonzero monomial times
the dual integral for `ψ` and `Φ̂`: the change of character moves `d_a` past the
long Weyl element, and the central translation `g ↦ g a` removes the dilation of
`Φ̂`. The fixed-monomial functional equation for `ψ` then gives the one for `ψ^a`.
This proves `EqualRankEpsilonCharacterChangeStatement`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped NNReal

universe uF uV uW

section ModelFunctions

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (a : Fˣ)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n π)

/-- In equal rank, the model function of `v` for the translated functional
`ℓ ∘ π(d_a)` is the left translate by `d_a` of the model function of `v` for `ℓ`. -/
theorem modelMap_characterChangeFunctional_self (v : V) :
    (modelMap π (characterChangeFunctional ψ π a ℓ) v).val =
      characterChangeFunction ψ n a (modelMap π ℓ v).val := by
  apply Subtype.ext
  funext g
  change ℓ.val (π (characterChangeElement a n) (π g v)) =
    ℓ.val (π (characterChangeElement a n * g) v)
  rw [map_mul, Module.End.mul_apply]

variable (ωπ : Fˣ →* ℂˣ)

/-- The first dual function of the translated model is `ω_π(a)^n` times the left
translate by `d_a` of the first dual function of the original model. -/
theorem firstDual_modelMap_characterChangeFunctional_self
    (hπ : Classification.HasGLCentralCharacter F (n + 1) π ωπ) (v : V)
    (h : Langlands.GeneralLinear (n + 1) F) :
    (firstDualFunction (ψ.scale a) n
        (modelMap π (characterChangeFunctional ψ π a ℓ) v).val).val h =
      ((ωπ a : ℂˣ) : ℂ) ^ n *
        (characterChangeFunction (ψ.scale (-1)) n a
          (firstDualFunction ψ n (modelMap π ℓ v).val)).val h := by
  rw [firstDualFunction_apply]
  change ℓ.val (π (characterChangeElement a n)
      (π (weylLong (n + 1) F * inverseTranspose (n + 1) F h) v)) =
    _ * ℓ.val (π (weylLong (n + 1) F * inverseTranspose (n + 1) F
      (characterChangeElement a n * h)) v)
  have hm : weylLong (n + 1) F * inverseTranspose (n + 1) F (characterChangeElement a n * h) =
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ n))⁻¹ *
        (characterChangeElement a n * (weylLong (n + 1) F * inverseTranspose (n + 1) F h)) := by
    rw [map_mul (inverseTranspose (n + 1) F), inverseTranspose_characterChangeElement,
      ← mul_assoc, weylLong_mul_characterChangeElement_inv]
    simp only [mul_assoc]
  rw [hm, map_mul π (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (a ^ n))⁻¹,
    Module.End.mul_apply, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1))), hπ,
    map_smul, smul_eq_mul, map_mul π (characterChangeElement a n), Module.End.mul_apply,
    ← mul_assoc, map_inv ωπ, map_pow ωπ, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    mul_inv_cancel₀ (pow_ne_zero _ (ωπ a).ne_zero), one_mul]

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- A model function is multiplied by `ω_π(b)` under right translation by the
scalar matrix `b`. -/
theorem modelMap_mul_scalar (hπ : Classification.HasGLCentralCharacter F (n + 1) π ωπ)
    {θ : upperUnipotent (n + 1) F →* ℂˣ}
    (ℓ : functionals (upperUnipotent (n + 1) F) θ π) (v : V) (b : Fˣ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (modelMap π ℓ v).val.val (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) =
      ((ωπ b : ℂˣ) : ℂ) * (modelMap π ℓ v).val.val g := by
  change ℓ.val (π (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) v) =
    _ * ℓ.val (π g v)
  rw [map_mul, Module.End.mul_apply, hπ, LinearMap.map_smul]
  exact (ℓ.val.map_smul _ _).trans (smul_eq_mul _ _)

/-- The first dual function of a model function is multiplied by `ω_π(b)⁻¹` under
right translation by the scalar matrix `b`. -/
theorem firstDual_modelMap_mul_scalar
    (hπ : Classification.HasGLCentralCharacter F (n + 1) π ωπ) (v : V) (b : Fˣ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (firstDualFunction ψ n (modelMap π ℓ v).val).val
        (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) =
      ((ωπ b : ℂˣ) : ℂ)⁻¹ * (firstDualFunction ψ n (modelMap π ℓ v).val).val g := by
  rw [firstDualFunction_apply, firstDualFunction_apply, map_mul, inverseTranspose_scalar',
    ← mul_assoc, modelMap_mul_scalar π ωπ hπ ℓ v b⁻¹, map_inv, Units.val_inv_eq_inv_val]

end ModelFunctions

section SecondDual

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ' : glInverseFunctionals ψ n σ) (ωσ : Fˣ →* ℂˣ)

/-- The second dual function of a model function is multiplied by `ω_σ(b)⁻¹` under
right translation by the scalar matrix `b`. -/
theorem secondDual_modelMap_mul_scalar
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ) (u : W) (b : Fˣ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (secondDualFunction ψ n (modelMap σ ℓ' u).val).val
        (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) =
      ((ωσ b : ℂˣ) : ℂ)⁻¹ * (secondDualFunction ψ n (modelMap σ ℓ' u).val).val g := by
  rw [secondDualFunction_apply, secondDualFunction_apply, map_mul, inverseTranspose_scalar',
    ← mul_assoc, modelMap_mul_scalar σ ωσ hσ ℓ' u b⁻¹, map_inv, Units.val_inv_eq_inv_val]

end SecondDual

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  (abv : AbsoluteValue F ℝ) [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))

omit [IsTopologicalRing F] in
/-- The equal-rank integral under an equality of characters and pointwise scalar
multiples of both functions. -/
theorem equalRankIntegral_congr_smul {ψ₁ ψ₂ : UnitaryAdditiveCharacter F} (hψ : ψ₁ = ψ₂)
    {W₁ : WhittakerFunctions ψ₁ n} {W₂ : WhittakerFunctions ψ₂ n}
    {W₁' : InverseWhittakerFunctions ψ₁ n} {W₂' : InverseWhittakerFunctions ψ₂ n}
    (c c' : ℂ) (hW : ∀ g, W₂.val g = c * W₁.val g) (hW' : ∀ g, W₂'.val g = c' * W₁'.val g)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ₂ abv μ W₂ W₂' Φ s =
      c * c' * equalRankIntegral ψ₁ abv μ W₁ W₁' Φ s := by
  subst hψ
  have he : ∀ x, equalRankIntegrand ψ₁ abv W₂ W₂' Φ s x =
      c * c' * equalRankIntegrand ψ₁ abv W₁ W₁' Φ s x := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      simp only [equalRankIntegrand_mk, hW, hW']
      ring
  unfold equalRankIntegral
  simp only [he, integral_const_mul]

omit [IsTopologicalRing F] in
/-- The equal-rank integral is linear in the test function. -/
theorem equalRankIntegral_smul_test (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n) (c : ℂ)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ abv μ W W' (c • Φ) s = c * equalRankIntegral ψ abv μ W W' Φ s := by
  have he : ∀ x, equalRankIntegrand ψ abv W W' (c • Φ) s x =
      c * equalRankIntegrand ψ abv W W' Φ s x := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      simp only [equalRankIntegrand_mk]
      change W.val g * W'.val g * (c * Φ (lastRow g)) * determinantWeight abv g s = _
      ring
  unfold equalRankIntegral
  simp only [he, integral_const_mul]

omit [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace (LeftUnipotentQuotient n F)] in
/-- The last row of `g b` for a scalar matrix `b` is `b` times the last row of `g`. -/
theorem lastRow_mul_scalar (g : Langlands.GeneralLinear (n + 1) F) (b : Fˣ) :
    lastRow (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) = (b : F) • lastRow g := by
  funext j
  simp only [lastRow, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul]
  ring

variable [BorelSpace (LeftUnipotentQuotient n F)]

/-- Central translation. If right translation by the scalar matrix `b` preserves
`μ` and multiplies `W` and `W'` by `c` and `c'`, the integral of `Φ` is
`c c' |det b|^s` times the integral of `x ↦ Φ(b x)`. -/
theorem equalRankIntegral_central_translate (ψ : UnitaryAdditiveCharacter F)
    (hμr : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (b : Fˣ) {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n} (c c' : ℂ)
    (hW : ∀ g, W.val (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) = c * W.val g)
    (hW' : ∀ g, W'.val (g * Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) = c' * W'.val g)
    (Φ Φb : SchwartzBruhat (Fin (n + 1) → F)) (hΦ : ∀ x, Φb x = Φ ((b : F) • x)) (s : ℂ) :
    equalRankIntegral ψ abv μ W W' Φ s =
      c * c' * determinantWeight abv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b) s *
        equalRankIntegral ψ abv μ W W' Φb s := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) b
  have he : ∀ x, equalRankIntegrand ψ abv W W' Φ s
      (rightTranslate (upperUnipotent (n + 1) F) z x) =
      c * c' * determinantWeight abv z s * equalRankIntegrand ψ abv W W' Φb s x := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      rw [rightTranslate_mk, equalRankIntegrand_mk, equalRankIntegrand_mk, hW, hW',
        lastRow_mul_scalar, determinantWeight_mul, hΦ]
      ring
  unfold equalRankIntegral
  rw [← (hμr z).integral_comp (rightTranslate (upperUnipotent (n + 1) F) z).measurableEmbedding]
  simp only [he, integral_const_mul]

end Integrals

section Fourier

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] {d : ℕ}

omit [MeasurableSpace F] [BorelSpace F] in
/-- The dilation `x ↦ Φ(b x)` of a Schwartz–Bruhat function by `b ∈ Fˣ`. -/
def dilateTest (b : Fˣ) (Φ : SchwartzBruhat (Fin d → F)) : SchwartzBruhat (Fin d → F) :=
  ⟨fun x => Φ ((b : F) • x), Φ.locallyConstant.comp_continuous (continuous_const_smul _),
    Φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero (b : F) b.ne_zero)⟩

omit [MeasurableSpace F] [BorelSpace F] in
@[simp] theorem dilateTest_apply (b : Fˣ) (Φ : SchwartzBruhat (Fin d → F)) (x : Fin d → F) :
    dilateTest b Φ x = Φ ((b : F) • x) := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F] in
/-- The row pairing is linear in the second row. -/
theorem rowPairing_smul_right (x y : Fin d → F) (b : F) :
    rowPairing x (b • y) = b * rowPairing x y := by
  simp only [rowPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Change of character and Haar measure for a row Fourier pair: if `Φ̂` is the
`ψ`-transform of `Φ` for `ν`, then `κ^d Φ̂(a ·)` is its `ψ^a`-transform for `κ ν`. -/
theorem IsRowFourierPair.characterChange {ψ : UnitaryAdditiveCharacter F}
    {ν : AdditiveHaarMeasure F} [SigmaFinite ν.measure]
    {Φ Φhat : SchwartzBruhat (Fin d → F)} (h : IsRowFourierPair ψ ν Φ Φhat) (a : Fˣ)
    (κ : ℝ≥0) (hκ : 0 < κ) :
    IsRowFourierPair (ψ.scale a) (ν.scale κ hκ) Φ
      ((((κ : ℝ) : ℂ) ^ d) • dilateTest a Φhat) := by
  intro y
  rw [rowFourierIntegral_scale]
  change ((κ : ℝ) : ℂ) ^ d * Φhat ((a : F) • y) = _
  rw [h ((a : F) • y)]
  congr 1
  unfold rowFourierIntegral
  congr 1
  funext x
  simp only [UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.scale_apply,
    rowPairing_smul_right]

end Fourier

section Spans

variable {q : ℕ} {V W M₁ M₁' M₂ M₂' Θ : Type*}
  {I₁ : M₁ → M₁' → Θ → ℂ → ℂ} {I₂ : M₂ → M₂' → Θ → ℂ → ℂ}
  {c₁ : V → M₁} {c₁' : W → M₁'} {c₂ : V → M₂} {c₂' : W → M₂'}

/-- Value sets of two integral families with a test-function argument, related by
one nonzero monomial through surjective parametrizations by vectors, span the same
Laurent module. -/
theorem zetaSpan_values_eq_of_monomial_test (hq : 0 < q)
    (hc₁ : Function.Surjective c₁) (hc₁' : Function.Surjective c₁')
    (hc₂ : Function.Surjective c₂) (hc₂' : Function.Surjective c₂')
    (α : ℂˣ) (a : ℤ)
    (hI : ∀ v w Φ s, I₂ (c₂ v) (c₂' w) Φ s = α * spectralPoint q s ^ a * I₁ (c₁ v) (c₁' w) Φ s) :
    zetaSpan {R | ∃ x y Φ, HasRationalContinuation q (I₁ x y Φ) R} =
      zetaSpan {R | ∃ x y Φ, HasRationalContinuation q (I₂ x y Φ) R} := by
  apply zetaSpan_eq_of_monomial_mul α a
  · rintro R ⟨x, y, Φ, hR⟩
    obtain ⟨v, rfl⟩ := hc₁ x
    obtain ⟨w, rfl⟩ := hc₁' y
    refine ⟨c₂ v, c₂' w, Φ, ?_⟩
    have h := hR.monomial_mul hq α a
    convert h using 1
    funext s
    exact hI v w Φ s
  · rintro R ⟨x, y, Φ, hR⟩
    obtain ⟨v, rfl⟩ := hc₂ x
    obtain ⟨w, rfl⟩ := hc₂' y
    refine ⟨c₁ v, c₁' w, Φ, ?_⟩
    have h := hR.monomial_mul hq (↑α⁻¹) (-a)
    convert h using 1
    funext s
    have hX : spectralPoint q s ^ a ≠ 0 := zpow_ne_zero _ (spectralPoint_ne_zero_of_pos hq s)
    rw [hI v w Φ s, zpow_neg, Units.val_inv_eq_inv_val]
    field_simp

end Spans

section Constants

variable {F : Type uF} [Field F]

/-- The equal-rank constants match: with `|a| = q^(-o)` and `κ² = |a|`,
`|a|^(-(n+1)²/2) = κ^(n+1) q^(o S + o (n+1))`, where `2 S = n (n+1)`. -/
theorem equalRankConstants_eq (q : ℕ) (hq : 0 < q) (abv : AbsoluteValue F ℝ) (a : Fˣ) (o : ℤ)
    (ho : abv (a : F) = (q : ℝ) ^ (-o)) (κ : ℝ≥0) (hκ2 : (κ : ℝ) ^ 2 = abv (a : F)) (n : ℕ) :
    ((abv (a : F) : ℝ) : ℂ) ^ (-(((n + 1) * (n + 1) : ℕ) : ℂ) / 2) =
      ((κ : ℝ) : ℂ) ^ (n + 1) *
        (q : ℂ) ^ (-(-(o * ((∑ i : Fin (n + 1), (n - i.val) : ℕ) : ℤ)) -
          o * ((n + 1 : ℕ) : ℤ))) := by
  have hA : 0 < abv (a : F) := abv.pos (Units.ne_zero a)
  have hκ : 0 < (κ : ℝ) := by
    rcases (κ.coe_nonneg).lt_or_eq with h | h
    · exact h
    · rw [← h] at hκ2; simp at hκ2; exact absurd hκ2.symm hA.ne'
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hla : Real.log (abv (a : F)) = -(o : ℝ) * Real.log q := by
    rw [ho, Real.log_zpow, Int.cast_neg]
  have hlk : Real.log κ = Real.log (abv (a : F)) / 2 := by
    rw [← hκ2, Real.log_pow]; push_cast; ring
  have hS := sum_fin_sub_mul_two n
  have e1 : ((abv (a : F) : ℝ) : ℂ) ^ (-(((n + 1) * (n + 1) : ℕ) : ℂ) / 2) =
      Complex.exp (Real.log (abv (a : F)) * (-(((n + 1) * (n + 1) : ℕ) : ℂ) / 2)) :=
    ofReal_cpow_eq_exp hA _
  have eκ : ((κ : ℝ) : ℂ) ^ (n + 1) = Complex.exp (Real.log κ * ((n + 1 : ℕ) : ℂ)) := by
    rw [← Complex.ofReal_pow, ofReal_pow_eq_exp hκ]
  have eq : ∀ B : ℤ, (q : ℂ) ^ B = Complex.exp (Real.log q * B) := fun B => by
    rw [← Complex.cpow_intCast, ← Complex.ofReal_natCast, ofReal_cpow_eq_exp hq']
  rw [e1, eκ, eq, ← Complex.exp_add]
  congr 1
  generalize (∑ i : Fin (n + 1), (n - i.val)) = S at hS ⊢
  have hS' : (S : ℂ) * 2 = n * (n + 1) := by exact_mod_cast hS
  have hla' : (Real.log (abv (a : F)) : ℂ) = -(o : ℂ) * Complex.log q := by
    rw [hla]; push_cast; ring
  have hlk' : (Real.log κ : ℂ) = Real.log (abv (a : F)) / 2 := by
    rw [hlk]; push_cast; ring
  push_cast
  rw [hlk', hla']
  linear_combination (-(o : ℂ) * Complex.log q / 2) * hS'

end Constants

section ModelIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (a : Fˣ)
  (μ : Measure (LeftUnipotentQuotient n F)) (hμ : HasCharacterChangeMeasureLaw abv a μ)
  (k : ℤ) (hk : abv (Matrix.det (characterChangeElement a n).val) = (q : ℝ) ^ (-k))
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)

include hq hμ hk in
/-- The original equal-rank integral for `ψ^a` and the translated functionals is
`C X^(-k)` times the one for `ψ`, with the same vectors and test function. -/
theorem equalRankModelIntegral_characterChange (v : V) (u : W)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankModelIntegral (ψ.scale a) abv μ π σ (characterChangeFunctional ψ π a ℓ)
        (characterChangeInverseFunctional ψ σ a ℓ')
        (modelMap π (characterChangeFunctional ψ π a ℓ) v)
        (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u) Φ s =
      (characterChangeScalar abv a n : ℂ) * spectralPoint q s ^ (-k) *
        equalRankModelIntegral ψ abv μ π σ ℓ ℓ' (modelMap π ℓ v) (modelMap σ ℓ' u) Φ s := by
  unfold equalRankModelIntegral
  rw [modelMap_characterChangeFunctional_self, modelMap_characterChangeInverseFunctional]
  exact equalRankIntegral_characterChange_monomial q hq ψ abv a μ hμ k hk _ _ Φ s

variable (ωπ ωσ : Fˣ →* ℂˣ)

include hq hμ hk in
/-- The dual equal-rank integral for `ψ^a` and the translated functionals is
`ω_π(a)^n ω_σ(a)^n C X^(-k)` times the one for `ψ`, with the same test function. -/
theorem dualEqualRankModelIntegral_characterChange
    (hπ : Classification.HasGLCentralCharacter F (n + 1) π ωπ)
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ) (v : V) (u : W)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    dualEqualRankModelIntegral (ψ.scale a) abv μ π σ (characterChangeFunctional ψ π a ℓ)
        (characterChangeInverseFunctional ψ σ a ℓ')
        (modelMap π (characterChangeFunctional ψ π a ℓ) v)
        (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u) Φ s =
      ((ωπ a : ℂˣ) : ℂ) ^ n * ((ωσ a : ℂˣ) : ℂ) ^ n * (characterChangeScalar abv a n : ℂ) *
        spectralPoint q s ^ (-k) *
        dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' (modelMap π ℓ v) (modelMap σ ℓ' u) Φ s := by
  have hψ : (ψ.scale (-1)).scale a = (ψ.scale a).scale (-1) := by
    rw [UnitaryAdditiveCharacter.scale_scale, UnitaryAdditiveCharacter.scale_scale, mul_comm]
  unfold dualEqualRankModelIntegral
  rw [equalRankIntegral_congr_smul abv μ hψ _ _
      (firstDual_modelMap_characterChangeFunctional_self ψ a π ℓ ωπ hπ v)
      (secondDual_modelMap_characterChangeInverseFunctional ψ a σ ℓ' ωσ hσ u) Φ s,
    equalRankIntegral_characterChange_monomial q hq (ψ.scale (-1)) abv a μ hμ k hk]
  ring

include hq hμ hk in
/-- The dual equal-rank integral for `ψ^a`, the translated functionals and the
test `t Φ(a ·)` is `ω_π(a)^(n+1) ω_σ(a)^(n+1) C t X^(-k - o(n+1))` times the one for
`ψ` and `Φ`, where `|a| = q^(-o)`: the central translation by `a` removes the
dilation. -/
theorem dualEqualRankModelIntegral_characterChange_dilate (o : ℤ)
    (ho : abv (a : F) = (q : ℝ) ^ (-o))
    (hμr : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (hπ : Classification.HasGLCentralCharacter F (n + 1) π ωπ)
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ) (v : V) (u : W) (t : ℂ)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    dualEqualRankModelIntegral (ψ.scale a) abv μ π σ (characterChangeFunctional ψ π a ℓ)
        (characterChangeInverseFunctional ψ σ a ℓ')
        (modelMap π (characterChangeFunctional ψ π a ℓ) v)
        (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u) (t • dilateTest a Φ) s =
      ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (n + 1) *
        (characterChangeScalar abv a n : ℂ) * t *
        spectralPoint q s ^ (-k - o * ((n + 1 : ℕ) : ℤ)) *
        dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' (modelMap π ℓ v) (modelMap σ ℓ' u) Φ s := by
  rw [dualEqualRankModelIntegral_characterChange q hq ψ abv a μ hμ k hk π σ ℓ ℓ' ωπ ωσ hπ hσ]
  unfold dualEqualRankModelIntegral
  rw [equalRankIntegral_smul_test,
    equalRankIntegral_central_translate abv μ (ψ.scale (-1)) hμr a _ _
      (firstDual_modelMap_mul_scalar ψ π ℓ ωπ hπ v a)
      (secondDual_modelMap_mul_scalar ψ σ ℓ' ωσ hσ u a) Φ (dilateTest a Φ) (fun _ => rfl) s]
  have hX := spectralPoint_ne_zero_of_pos hq s
  have hD : determinantWeight abv (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) a) s =
      spectralPoint q s ^ (o * ((n + 1 : ℕ) : ℤ)) :=
    determinantWeight_eq_spectralPoint_zpow q hq abv _ _ (by
      rw [abv_det_scalar, ho, ← zpow_natCast, ← zpow_mul, neg_mul]) s
  have h1 := (ωπ a).ne_zero
  have h2 := (ωσ a).ne_zero
  have h3 : spectralPoint q s ^ (o * ((n + 1 : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hX
  rw [hD, zpow_sub₀ hX]
  field_simp
  ring

end ModelIntegrals

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The fixed-monomial equal-rank epsilon equation for `ψ`, `ν` and `(ℓ, ℓ')`
gives the one for `ψ^a`, `κ ν` with `κ² = |a|` and the translated functionals,
with the coefficient multiplied by `ω_π(a)^(n+1) ω_σ(a)^(n+1) |a|^(-(n+1)²/2)` and
the exponent shifted by `(n+1)² o`, where `|a| = q^(-o)`. The quotient-measure laws
are hypotheses. -/
theorem EqualRankEpsilonEquation.characterChange (q : ℕ) (hq : 0 < q)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (a : Fˣ) (o : ℤ)
    (ho : abv (a : F) = (q : ℝ) ^ (-o))
    (μ : Measure (LeftUnipotentQuotient n F)) (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (hμr : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure] (κ : ℝ≥0) (hκ : 0 < κ)
    (hκ2 : (κ : ℝ) ^ 2 = abv (a : F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (ωπ ωσ : Fˣ →* ℂˣ)
    (hπ : Classification.HasGLCentralCharacter F (n + 1) π ωπ)
    (hσ : Classification.HasGLCentralCharacter F (n + 1) σ ωσ)
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ} {c : ℂˣ} {m : ℤ}
    (h : EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m) (c' : ℂˣ)
    (hc' : (c' : ℂ) = c * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (n + 1) *
      ((abv (a : F) : ℝ) : ℂ) ^ (-(((n + 1) * (n + 1) : ℕ) : ℂ) / 2)) :
    EqualRankEpsilonEquation q (ψ.scale a) abv μ (ν.scale κ hκ) π σ
      (characterChangeFunctional ψ π a ℓ) (characterChangeInverseFunctional ψ σ a ℓ') c'
      (m + ((n + 1) * (n + 1) : ℕ) * o) := by
  have hk := abv_det_characterChangeElement_eq_zpow q abv a o ho n
  have hcst := equalRankConstants_eq q hq abv a o ho κ hκ2 n
  have hS2 := sum_fin_sub_mul_two n
  generalize (∑ i : Fin (n + 1), (n - i.val)) = S at hk hcst hS2
  obtain ⟨ζ, P, Pdual, hζ, hP, hPd, hFE⟩ := h
  have hκ0 : ((κ : ℝ) : ℂ) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hκ.ne'))
  obtain ⟨αd, hαd⟩ : ∃ αd : ℂˣ, (αd : ℂ) =
      ((ωπ a : ℂˣ) : ℂ) ^ n * ((ωσ a : ℂˣ) : ℂ) ^ n * (characterChangeScalar abv a n : ℂ) :=
    ⟨ωπ a ^ n * ωσ a ^ n * characterChangeScalar abv a n, by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂˣ, (β : ℂ) =
      ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) * ((ωσ a : ℂˣ) : ℂ) ^ (n + 1) *
        (characterChangeScalar abv a n : ℂ) * ((κ : ℝ) : ℂ) ^ (n + 1) :=
    ⟨ωπ a ^ (n + 1) * ωσ a ^ (n + 1) * characterChangeScalar abv a n * Units.mk0 _ hκ0, by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]⟩
  have hI := equalRankModelIntegral_characterChange q hq ψ abv a μ hμ _ hk π σ ℓ ℓ'
  have hId : ∀ v u Φ s,
      dualEqualRankModelIntegral (ψ.scale a) abv μ π σ (characterChangeFunctional ψ π a ℓ)
          (characterChangeInverseFunctional ψ σ a ℓ')
          (modelMap π (characterChangeFunctional ψ π a ℓ) v)
          (modelMap σ (characterChangeInverseFunctional ψ σ a ℓ') u) Φ s =
        (αd : ℂ) * spectralPoint q s ^ (-(o * (S : ℤ))) *
          dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' (modelMap π ℓ v) (modelMap σ ℓ' u)
            Φ s := by
    intro v u Φ s
    rw [hαd, dualEqualRankModelIntegral_characterChange q hq ψ abv a μ hμ _ hk π σ ℓ ℓ' ωπ ωσ
      hπ hσ]
  have hS := zetaSpan_values_eq_of_monomial_test
    (I₁ := equalRankModelIntegral ψ abv μ π σ ℓ ℓ')
    (I₂ := equalRankModelIntegral (ψ.scale a) abv μ π σ (characterChangeFunctional ψ π a ℓ)
      (characterChangeInverseFunctional ψ σ a ℓ'))
    hq (modelMap_surjective π ℓ) (modelMap_surjective σ ℓ')
    (modelMap_surjective π (characterChangeFunctional ψ π a ℓ))
    (modelMap_surjective σ (characterChangeInverseFunctional ψ σ a ℓ'))
    (characterChangeScalar abv a n) _ hI
  have hSd := zetaSpan_values_eq_of_monomial_test
    (I₁ := dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ')
    (I₂ := dualEqualRankModelIntegral (ψ.scale a) abv μ π σ (characterChangeFunctional ψ π a ℓ)
      (characterChangeInverseFunctional ψ σ a ℓ'))
    hq (modelMap_surjective π ℓ) (modelMap_surjective σ ℓ')
    (modelMap_surjective π (characterChangeFunctional ψ π a ℓ))
    (modelMap_surjective σ (characterChangeInverseFunctional ψ σ a ℓ'))
    αd _ hId
  refine ⟨ζ, P, Pdual, hζ.characterChange a, ⟨hP.1, hS.symm.trans hP.2⟩,
    ⟨hPd.1, hSd.symm.trans hPd.2⟩, ?_⟩
  intro f f' Φ
  obtain ⟨v, rfl⟩ := modelMap_surjective π (characterChangeFunctional ψ π a ℓ) f
  obtain ⟨u, rfl⟩ := modelMap_surjective σ (characterChangeInverseFunctional ψ σ a ℓ') f'
  obtain ⟨Φhat, R, Rd, hF, hR, hRd, hN⟩ := hFE (modelMap π ℓ v) (modelMap σ ℓ' u) Φ
  refine ⟨(((κ : ℝ) : ℂ) ^ (n + 1)) • dilateTest a Φhat, _, _, IsRowFourierPair.characterChange hF a κ hκ,
    ?_, ?_, hN.monomial_transport hq (characterChangeScalar abv a n) β (-(o * (S : ℤ)))
      (-(o * (S : ℤ)) - o * ((n + 1 : ℕ) : ℤ)) ?_ ?_⟩
  · convert hR.monomial_mul hq (characterChangeScalar abv a n : ℂ) (-(o * (S : ℤ))) using 1
    funext s
    exact hI v u Φ s
  · convert hRd.monomial_mul hq (β : ℂ) (-(o * (S : ℤ)) - o * ((n + 1 : ℕ) : ℤ)) using 1
    funext s
    rw [dualEqualRankModelIntegral_characterChange_dilate q hq ψ abv a μ hμ _ hk π σ ℓ ℓ' ωπ ωσ
      o ho hμr hπ hσ, hβ]
  · have hS2' : (S : ℤ) * 2 = n * (n + 1) := by exact_mod_cast hS2
    push_cast
    linear_combination (-o) * hS2'
  · rw [hc', hcst, hβ]
    ring

end Generic

section Padic

attribute [local instance] pfccTopology pfccValuativeRel pfccLocalField pfccMeasurable
  pfccBorel pfccGroupMeasurable pfccGroupBorel pfccUnipotentMeasurable pfccUnipotentBorel
  pfccQuotientMeasurable

local instance erccQuotientBorel {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) :=
  ⟨rfl⟩
local instance erccSecondCountable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance erccSigmaCompact {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace

/-- Theorem: the change of additive character for the epsilon factor of a pair
of equal rank with self-dual measures, `EqualRankEpsilonCharacterChangeStatement`. -/
theorem equalRankEpsilonCharacterChange :
    EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW} := by
  intro p _ F r V _ _ W _ _ π σ ωπ ωσ _ _ _ _ hπ hσ ψ ν a ν' e he
  let T := F.canonicalTopologicalData
  have hq : 0 < T.residueCardinality := lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  have ho : normalizedAbsoluteValue T (a : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-T.ord (a : F.Carrier)) :=
    T.normalizedAbs_of_ne_zero a.ne_zero
  set N : ℕ := (r + 1) * (r + 1)
  let c' : ℂˣ := e.1 * ωπ a ^ (r + 1) * ωσ a ^ (r + 1) *
    Units.mk0 _ (normalizedAbs_cpow_ne_zero F a (-((N : ℕ) : ℂ) / 2))
  have hc' : (c' : ℂ) = (e.1 : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (r + 1) *
      ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
        ((T.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^ (-((N : ℕ) : ℂ) / 2) := by
    simp only [c', Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rfl
  refine ⟨(c', e.2 + (N : ℤ) * T.ord (a : F.Carrier)), ?_, rfl, hc'⟩
  rw [isPadicSymmetricEpsilonFactor_of_le le_rfl] at he ⊢
  rw [LocalFactor.PadicAbelian.SelfDualHaar.val_eq_scale F ψ a ν ν']
  obtain ⟨hmeas, ⟨ℓ₀, hℓ₀⟩, ⟨ℓ₀', hℓ₀'⟩, hall⟩ := isPairEpsilonFactor_self.mp he
  refine isPairEpsilonFactor_self.mpr ⟨hmeas, ⟨characterChangeFunctional ψ π a ℓ₀,
      val_ne_zero_of_linearEquiv (characterChangeFunctionalEquiv ψ π a) hℓ₀⟩,
    ⟨characterChangeInverseFunctional ψ σ a ℓ₀',
      val_ne_zero_of_linearEquiv (characterChangeInverseFunctionalEquiv ψ σ a) hℓ₀'⟩, ?_⟩
  intro _ μ hμ ℓ ℓ' hℓ hℓ'
  let ℓO := (characterChangeFunctionalEquiv ψ π a).symm ℓ
  let ℓO' := (characterChangeInverseFunctionalEquiv ψ σ a).symm ℓ'
  have hℓO : ℓO.val ≠ 0 :=
    val_ne_zero_of_linearEquiv (characterChangeFunctionalEquiv ψ π a).symm hℓ
  have hℓO' : ℓO'.val ≠ 0 :=
    val_ne_zero_of_linearEquiv (characterChangeInverseFunctionalEquiv ψ σ a).symm hℓ'
  have hE := EqualRankEpsilonEquation.characterChange T.residueCardinality hq ψ
    (normalizedAbsoluteValue T) a (T.ord (a : F.Carrier)) ho μ
    (characterChangeCompatibleMeasure p F T r a μ hμ) hμ.right_invariant ν.val
    (LocalFactor.PadicAbelian.sqrtNormalizedAbs F a)
    (LocalFactor.PadicAbelian.sqrtNormalizedAbs_pos F a)
    (LocalFactor.PadicAbelian.sqrtNormalizedAbs_sq F a) π σ ωπ ωσ hπ hσ
    (hall μ hμ ℓO ℓO' hℓO hℓO') c' hc'
  have hL : characterChangeFunctional ψ π a ℓO = ℓ :=
    (characterChangeFunctionalEquiv ψ π a).apply_symm_apply ℓ
  have hL' : characterChangeInverseFunctional ψ σ a ℓO' = ℓ' :=
    (characterChangeInverseFunctionalEquiv ψ σ a).apply_symm_apply ℓ'
  rw [hL, hL'] at hE
  exact hE

end Padic

end Langlands.RankinSelberg
