import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroCovariance
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.Group.GL.CountabilityProof

/-!
# Continued unequal-rank bilinear forms at block zero

Proof of `UnequalRankBlockZeroContinuedFormsStatement`. The two forms are the
evaluations at `q^{-s}` and `q^{-(1-s)}` of the bilinear families of rational
continuations of the original `(0,k)` integral and of the inverse-transpose
`(k,0)` integral of the dual model vectors. The finite exceptional set consists
of the roots of the original normalized generator and the reflections
`w ↦ (q w)⁻¹` of the roots of the dual normalized generator.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open RationalEvaluation
open scoped NNReal

universe uF uV uW

section RectangularIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {k t : ℕ} [BorelSpace (Matrix (Fin k) (Fin t) F)]

/-- Right multiplication of rectangular matrices by an invertible matrix, as a
measurable equivalence. -/
def matrixMulRightEquiv (B : Langlands.GeneralLinear t F) :
    Matrix (Fin k) (Fin t) F ≃ᵐ Matrix (Fin k) (Fin t) F where
  toFun X := X * B.val
  invFun X := X * (B⁻¹ : Langlands.GeneralLinear t F).val
  left_inv X := by simp [Matrix.mul_assoc]
  right_inv X := by simp [Matrix.mul_assoc]
  measurable_toFun := (continuous_id.matrix_mul continuous_const).measurable
  measurable_invFun := (continuous_id.matrix_mul continuous_const).measurable

/-- Left multiplication of rectangular matrices by an invertible matrix, as a
measurable equivalence. -/
def matrixMulLeftEquiv (A : Langlands.GeneralLinear k F) :
    Matrix (Fin k) (Fin t) F ≃ᵐ Matrix (Fin k) (Fin t) F where
  toFun X := A.val * X
  invFun X := (A⁻¹ : Langlands.GeneralLinear k F).val * X
  left_inv X := by simp [← Matrix.mul_assoc]
  right_inv X := by simp [← Matrix.mul_assoc]
  measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable
  measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable

omit [IsTopologicalRing F] [BorelSpace (Matrix (Fin k) (Fin t) F)] in
/-- Integral form of a scaling law `ρ.map e = c • ρ`. -/
theorem integral_comp_of_map_eq_smul {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (e : α ≃ᵐ α) {c : ℝ≥0} (h : ρ.map e = c • ρ) (G : α → ℂ) :
    ∫ x, G (e x) ∂ρ = ((c : ℝ) : ℂ) * ∫ x, G x ∂ρ := by
  rw [← integral_map_equiv e G, h, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]

/-- A rectangular additive Haar measure preserved by left multiplication by `A`
is preserved by every affine map `x ↦ A x + c`. -/
theorem integral_affine_eq_self {ρ : Measure (Matrix (Fin k) (Fin t) F)} [ρ.IsAddHaarMeasure]
    (A : Langlands.GeneralLinear k F) (hA : ρ.map (matrixMulLeftEquiv A) = ρ)
    (c : Matrix (Fin k) (Fin t) F) (G : Matrix (Fin k) (Fin t) F → ℂ) :
    ∫ x, G (A.val * x + c) ∂ρ = ∫ x, G x ∂ρ := by
  have h1 : ∫ x, G (A.val * x + c) ∂ρ = ∫ y, G (y + c) ∂ρ := by
    have h := integral_map_equiv (μ := ρ) (matrixMulLeftEquiv A) (fun y => G (y + c))
    rw [hA] at h
    exact h.symm
  have h2 := (Homeomorph.addRight c).measurableEmbedding.integral_map (μ := ρ) G
  rw [Homeomorph.coe_addRight, map_add_right_eq_self] at h2
  rw [h1, ← h2]

end RectangularIntegrals

section Spectral

/-- The dual spectral point reflects to the original one. -/
theorem spectralPoint_reflect {q : ℕ} (hq : 0 < q) (s : ℂ) :
    ((q : ℂ) * spectralPoint q (1 - s))⁻¹ = spectralPoint q s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [spectralPoint_sub_one_sub hq, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul, inv_inv]

theorem spectralPoint_ne_zero_of_pos {q : ℕ} (hq : 0 < q) (s : ℂ) : spectralPoint q s ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact fun h => hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

end Spectral

section Assembly

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [BorelSpace (LeftUnipotentQuotient n F)] in
/-- The inverse-transpose continuation family of block `(k,0)`, pulled back to
the original model vectors along `f ↦ R(diag(I, w)) F̂` and `f' ↦ F̂'`. -/
def dualBlockContinuationFamily (hnr : n < r) {k : ℕ} {hr : r = n + (k + 0 + 1)} {q : ℕ}
    {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)} {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hAd : UnequalRankAnalyticAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ] (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ]
      RationalFunctions :=
  LinearMap.compl₁₂ (blockContinuationFamily hq hAd) (dualFirstModelMap ψ π ℓ hnr)
    (secondDualModelMap ψ σ ℓ')

omit [BorelSpace (LeftUnipotentQuotient n F)] in
theorem dualBlockContinuationFamily_apply (hnr : n < r) {k : ℕ} {hr : r = n + (k + 0 + 1)}
    {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)} {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hAd : UnequalRankAnalyticAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    dualBlockContinuationFamily hnr hq hAd f f' =
      blockContinuationFamily hq hAd (dualFirstModelMap ψ π ℓ hnr f)
        (secondDualModelMap ψ σ ℓ' f') :=
  rfl

omit [BorelSpace (LeftUnipotentQuotient n F)] in
/-- Every value of the pulled-back dual family is cleared by a normalized
generator of the dual rational-value set. -/
theorem dualBlockContinuationFamily_clears (hnr : n < r) {k : ℕ} {hr : r = n + (k + 0 + 1)}
    {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)} {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hAd : UnequalRankAnalyticAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (unequalRankValuesAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')) P)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ a : LaurentCoefficients, laurentToRatFunc a =
      algebraMap (Polynomial ℂ) RationalFunctions P * dualBlockContinuationFamily hnr hq hAd f f' :=
  blockContinuationFamily_clears hq hAd hP _ _

omit [BorelSpace (LeftUnipotentQuotient n F)] in
/-- The value of the pulled-back dual family is the unique rational
continuation of the dual integral. -/
theorem dualBlockContinuationFamily_eq (hnr : n < r) {k : ℕ} {hr : r = n + (k + 0 + 1)}
    {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {μ : Measure (LeftUnipotentQuotient n F)} {ρ : Measure (Matrix (Fin k) (Fin (n + 1)) F)}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}
    (hq : 1 < q) [SFinite μ] [SFinite ρ]
    (hAd : UnequalRankAnalyticAt k 0 hr q (ψ.scale (-1)) abv μ ρ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    {f : (coefficientModel π ℓ).toSubmodule} {f' : (coefficientModel σ ℓ').toSubmodule}
    {Rd : RationalFunctions}
    (hRd : HasRationalContinuation q (unequalRankIntegralAt k 0 hr (ψ.scale (-1)) abv μ ρ
      (dualFirstModelMap ψ π ℓ hnr f).val (secondDualModelMap ψ σ ℓ' f').val) Rd) :
    dualBlockContinuationFamily hnr hq hAd f f' = Rd :=
  blockContinuationFamily_eq hq hAd hRd

omit [IsTopologicalRing F] [BorelSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient n F)] in
/-- On the zero-row rectangular space right translation acts trivially and the
weight `|det g|^0` is one. -/
theorem rectangularMeasure_zero_rows_translate (ν : AdditiveHaarMeasure F)
    (abv : AbsoluteValue F ℝ) (g : Langlands.GeneralLinear (n + 1) F)
    (G : Matrix (Fin 0) (Fin (n + 1)) F → ℂ) :
    ∫ x, G (x * g.val) ∂(rectangularMeasure ν 0 (n + 1)) =
      determinantWeight abv g (-((0 : ℕ) : ℂ)) * ∫ x, G x ∂(rectangularMeasure ν 0 (n + 1)) := by
  have hx : ∀ x : Matrix (Fin 0) (Fin (n + 1)) F, x * g.val = x :=
    fun x => Matrix.ext fun i _ => i.elim0
  simp only [hx, Nat.cast_zero, neg_zero, determinantWeight, Complex.cpow_zero, one_mul]

/-- The construction of the block-zero continued forms over a general
topological field, from right invariance of the quotient measure, integrality of
`log_q |det g|`, and the right-scaling and affine-invariance laws of the
rectangular measure of block `k = r - n - 1`. -/
theorem blockZeroContinuedForms_of_laws (hnr : n < r) {q : ℕ} (hq : 1 < q)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) [SFinite μ]
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (ν : AdditiveHaarMeasure F) [SFinite (rectangularMeasure ν 0 (n + 1))]
    [SFinite (rectangularMeasure ν (r - n - 1) (n + 1))]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (habv : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∃ m : ℤ, abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (hρ : ∀ (g : Langlands.GeneralLinear (n + 1) F)
      (G : Matrix (Fin (r - n - 1)) (Fin (n + 1)) F → ℂ),
      ∫ x, G (x * g.val) ∂(rectangularMeasure ν (r - n - 1) (n + 1)) =
        determinantWeight abv g (-((r - n - 1 : ℕ) : ℂ)) *
          ∫ x, G x ∂(rectangularMeasure ν (r - n - 1) (n + 1)))
    (hρaff : ∀ A : Matrix (Fin (r - n - 1)) (Fin (r - n - 1)) F, A.det = 1 →
      ∀ (c : Matrix (Fin (r - n - 1)) (Fin (n + 1)) F)
        (G : Matrix (Fin (r - n - 1)) (Fin (n + 1)) F → ℂ),
        ∫ x, G (A * x + c) ∂(rectangularMeasure ν (r - n - 1) (n + 1)) =
          ∫ x, G x ∂(rectangularMeasure ν (r - n - 1) (n + 1)))
    (hA : UnequalRankAnalyticAt 0 (r - n - 1) (by omega) q ψ abv μ
      (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ')
    (hAd : UnequalRankAnalyticAt (r - n - 1) 0 (by omega) q (ψ.scale (-1)) abv μ
      (rectangularMeasure ν (r - n - 1) (n + 1))
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')) :
    UnequalRankBlockZeroContinuedFormsConclusion hnr q ψ abv μ ν π σ ℓ ℓ' := by
  unfold UnequalRankBlockZeroContinuedFormsConclusion
  intro k hr M M'
  have hq0 : 0 < q := by omega
  have hrn : r - n = 0 + (r - n - 1) + 1 := by omega
  obtain ⟨P, hP⟩ := hA.exists_normalizedGenerator
  obtain ⟨Pd, hPd⟩ := hAd.exists_normalizedGenerator
  refine ⟨P.roots.toFinset ∪ Pd.roots.toFinset.image (fun w => ((q : ℂ) * w)⁻¹),
    fun s hs => ?_⟩
  have hz : spectralPoint q s ≠ 0 := spectralPoint_ne_zero_of_pos hq0 s
  have hzd : spectralPoint q (1 - s) ≠ 0 := spectralPoint_ne_zero_of_pos hq0 (1 - s)
  have hPs : P.eval (spectralPoint q s) ≠ 0 := fun h =>
    hs (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP.polynomial_ne_zero).mpr h)))
  have hPds : Pd.eval (spectralPoint q (1 - s)) ≠ 0 := fun h =>
    hs (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hPd.polynomial_ne_zero).mpr h), spectralPoint_reflect hq0 s⟩))
  have hreg : ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule),
      RegularAt (blockContinuationFamily hq hA f f') (spectralPoint q s) :=
    fun f f' => by
      obtain ⟨a, ha⟩ := blockContinuationFamily_clears hq hA hP f f'
      exact regularAt_of_clears hz hPs ha
  have hregd : ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule),
      RegularAt (dualBlockContinuationFamily (π := π) (σ := σ) (ℓ := ℓ) (ℓ' := ℓ') hnr hq hAd f f')
        (spectralPoint q (1 - s)) := fun f f' => by
    obtain ⟨a, ha⟩ := dualBlockContinuationFamily_clears hnr hq hAd hPd f f'
    exact regularAt_of_clears hzd hPds ha
  refine ⟨evalForm (M := (coefficientModel π ℓ).toSubmodule)
      (M' := (coefficientModel σ ℓ').toSubmodule)
      (blockContinuationFamily (π := π) (σ := σ) (ℓ := ℓ) (ℓ' := ℓ') hq hA)
      (spectralPoint q s) hreg,
    evalForm (M := (coefficientModel π ℓ).toSubmodule)
      (M' := (coefficientModel σ ℓ').toSubmodule)
      (dualBlockContinuationFamily (π := π) (σ := σ) (ℓ := ℓ) (ℓ' := ℓ') hnr hq hAd)
      (spectralPoint q (1 - s)) hregd,
    ?_, ?_, ?_, ?_⟩
  · -- Covariance of the original form.
    unfold IsUnequalRankBilinearCovariant
    intro ι
    refine ⟨fun g f f' => ?_, fun u hu f f' => ?_⟩
    · obtain ⟨m, hg⟩ := habv g
      rw [evalForm_apply, evalForm_apply,
        blockContinuationFamily_translate hq hA hμ g (rectangularMeasure_zero_rows_translate ν abv g)
          m hg (f₁ := f) (f₁' := f') (f₂ := modelRepresentation π ℓ (ι g) f)
          (f₂' := modelRepresentation σ ℓ' g f') (fun h => rfl) (fun h => rfl),
        eval_C_mul_X_zpow_mul hz (hreg f f'),
        ← determinantWeight_neg_eq_spectralPoint_zpow hq0 abv g m hg s,
        ← determinantWeight_exponent_add]
      congr 2
      rw [← hrn]
      push_cast
      ring
    · rw [evalForm_apply, evalForm_apply, originalContinuationFamily_unipotent hq hA u hu f f',
        eval_C_mul_X_zpow_mul hz (hreg f f'), zpow_zero, mul_one]
  · -- Covariance of the dual form.
    unfold IsUnequalRankBilinearCovariant
    intro ι
    refine ⟨fun g f f' => ?_, fun u hu f f' => ?_⟩
    · obtain ⟨m, hg⟩ := habv g
      have hg' : abv (Matrix.det (inverseTranspose (n + 1) F g).val) = (q : ℝ) ^ (-m) := by
        rw [abv_det_inverseTranspose, hg, zpow_neg]
      rw [evalForm_apply, evalForm_apply, dualBlockContinuationFamily_apply,
        dualBlockContinuationFamily_apply,
        dualContinuationFamily_translate hnr hq hAd hμ g (hρ (inverseTranspose (n + 1) F g))
          (-m) hg' f f',
        eval_C_mul_X_zpow_mul hzd (R := blockContinuationFamily hq hAd
          (dualFirstModelMap ψ π ℓ hnr f) (secondDualModelMap ψ σ ℓ' f')) (hregd f f'),
        ← determinantWeight_neg_eq_spectralPoint_zpow hq0 abv _ (-m) hg' (1 - s),
        ← determinantWeight_exponent_add, determinantWeight_inverseTranspose]
      congr 2
      have h1 : ((r - n - 1 : ℕ) : ℂ) = ((r - n : ℕ) : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r - n), Nat.cast_one]
      rw [show r - n - 1 + 0 + 1 = r - n by omega, h1]
      ring
    · rw [evalForm_apply, evalForm_apply, dualBlockContinuationFamily_apply,
        dualBlockContinuationFamily_apply,
        dualContinuationFamily_unipotent hnr hq hAd hρaff u hu f f',
        eval_C_mul_X_zpow_mul hzd (R := blockContinuationFamily hq hAd
          (dualFirstModelMap ψ π ℓ hnr f) (secondDualModelMap ψ σ ℓ' f')) (hregd f f')]
      simp only [zpow_zero, mul_one]
  · -- Evaluation of the original continuations.
    intro f f' R hR
    have hCR : blockContinuationFamily hq hA f f' = R := blockContinuationFamily_eq hq hA hR
    refine ⟨?_, ?_⟩
    · rw [← hCR]
      exact hreg f f'
    · rw [evalForm_apply, hCR]
  · -- Evaluation of the dual continuations.
    intro f f' Rd hRd
    have hCR : dualBlockContinuationFamily hnr hq hAd f f' = Rd :=
      dualBlockContinuationFamily_eq hnr hq hAd hRd
    refine ⟨?_, ?_⟩
    · rw [← hCR]
      exact hregd f f'
    · rw [evalForm_apply, hCR]

end Assembly

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The right-scaling and affine-invariance laws of the rectangular product
measure built from any additive Haar measure, for the normalized absolute value. -/
theorem padic_rectangular_laws (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ ν : AdditiveHaarMeasure F.Carrier,
      (∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
        (G : Matrix (Fin k) (Fin (n + 1)) F.Carrier → ℂ),
        ∫ x, G (x * g.val) ∂(rectangularMeasure ν k (n + 1)) =
          determinantWeight (normalizedAbsoluteValue T) g (-((k : ℕ) : ℂ)) *
            ∫ x, G x ∂(rectangularMeasure ν k (n + 1))) ∧
      (∀ A : Matrix (Fin k) (Fin k) F.Carrier, A.det = 1 →
        ∀ (c : Matrix (Fin k) (Fin (n + 1)) F.Carrier)
          (G : Matrix (Fin k) (Fin (n + 1)) F.Carrier → ℂ),
          ∫ x, G (A * x + c) ∂(rectangularMeasure ν k (n + 1)) =
            ∫ x, G x ∂(rectangularMeasure ν k (n + 1))) := by
  intro ν
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  have : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  refine ⟨fun g G => ?_, fun A hA c G => ?_⟩
  · have h := padicRectangularHaarScaling F T k (n + 1) (rectangularMeasure ν k (n + 1)) 1 g⁻¹
    have he : (fun X : Matrix (Fin k) (Fin (n + 1)) F.Carrier =>
        ((1 : Langlands.GeneralLinear k F.Carrier) : Matrix (Fin k) (Fin k) F.Carrier) * X *
          ((g⁻¹⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) =
        ⇑(matrixMulRightEquiv (k := k) g) := by
      funext X
      simp [matrixMulRightEquiv]
    rw [he] at h
    rw [show (fun x => G (x * g.val)) = fun x => G (matrixMulRightEquiv (k := k) g x) from rfl,
      integral_comp_of_map_eq_smul _ h]
    congr 1
    simp only [map_one, map_inv, Units.val_one, one_pow, Units.val_inv_eq_inv_val, one_div,
      inv_inv, NNReal.coe_pow, NNReal.coe_inv, PadicField.TopologicalData.determinantNorm_coe,
      determinantWeight, normalizedAbsoluteValue_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rw [inv_pow]
  · let A' : Langlands.GeneralLinear k F.Carrier :=
      Matrix.nonsingInvUnit A (by rw [hA]; exact isUnit_one)
    have hA' : GeneralLinear.determinant A' = 1 := Units.ext hA
    have h := padicRectangularHaarScaling F T k (n + 1) (rectangularMeasure ν k (n + 1)) A' 1
    have he : (fun X : Matrix (Fin k) (Fin (n + 1)) F.Carrier =>
        (A' : Matrix (Fin k) (Fin k) F.Carrier) * X *
          ((1⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) =
        ⇑(matrixMulLeftEquiv (t := n + 1) A') := by
      funext X
      simp [matrixMulLeftEquiv]
    have hdet : T.determinantNorm k A' = 1 := by
      change T.normalizedAbsUnits (GeneralLinear.determinant A') = 1
      rw [hA', map_one]
    rw [he, hdet, map_one] at h
    simp only [Units.val_one, one_pow, div_one, inv_one, one_smul] at h
    exact integral_affine_eq_self A' h c G

/-- The supplied compatible quotient measure is sigma finite. -/
theorem padic_quotient_sigmaFinite (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier), μ.Regular → SigmaFinite μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro μ hμ
  have : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    T.generalLinearSigmaCompactSpace (n + 1)
  have : SigmaCompactSpace (LeftUnipotentQuotient n F.Carrier) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel
      (upperUnipotent (n + 1) F.Carrier)))]
    exact isSigmaCompact_range continuous_quot_mk
  infer_instance

end Padic

/-- **Continued unequal-rank bilinear forms at block zero.** Proof of
`UnequalRankBlockZeroContinuedFormsStatement`. -/
theorem unequalRankBlockZeroContinuedForms {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankBlockZeroContinuedFormsStatement.{uF, uV, uW} F T n r := by
  have hrect := padic_rectangular_laws T n (r - n - 1)
  have hinst := padic_row_instances T n
  have hquot := padic_quotient_sigmaFinite T n
  unfold UnequalRankBlockZeroContinuedFormsStatement
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro hnr ψ _ μ hμ ν V _ _ W _ _ π σ _ _ ℓ ℓ' _ _ k hr q abv hA hAd
  obtain ⟨-, hS⟩ := hinst ν
  have : SigmaFinite μ := hquot μ hμ.regular
  exact blockZeroContinuedForms_of_laws hnr T.residueCardinality_gt_one ψ abv μ
    hμ.right_invariant ν π σ ℓ ℓ' (fun g => ⟨_, normalizedAbsoluteValue_det_eq_zpow T g⟩)
    (hrect ν).1 (hrect ν).2 hA hAd

end Langlands.RankinSelberg
