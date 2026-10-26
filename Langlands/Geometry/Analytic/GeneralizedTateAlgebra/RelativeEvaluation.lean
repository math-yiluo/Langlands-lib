import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeAlgebra
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation

/-! # Evaluation through a contractive coefficient algebra map -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.GeneralizedTateAlgebra

open Filter
open scoped Topology

variable {σ : Type u} (r : PositivePolyradius σ)
  {K : Type v} [NormedField K]
  {A : Type w} [NormedCommRing A] [IsUltrametricDist A] [NormedAlgebra K A]
  {B : Type z} [NormedCommRing B] [IsUltrametricDist B] [NormedAlgebra K B]
  (φ : BoundedAlgHom K A B) (b : σ → B)

/-- A relative coefficient monomial evaluated through the specified coefficient map. -/
def coefficientEvaluationTerm (f : GeneralizedTateAlgebra r A) (d : σ →₀ ℕ) : B :=
  φ (MvPowerSeries.coeff d (series r A f)) *
    StrictTateAlgebra.monomialValue σ B b d

/-- Evaluation of relative series through a bounded coefficient map. -/
def evaluateCoefficients (f : GeneralizedTateAlgebra r A) : B :=
  ∑' d, coefficientEvaluationTerm r φ b f d

variable (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
  (hb : ∀ d : σ →₀ ℕ, ‖StrictTateAlgebra.monomialValue σ B b d‖ ≤ r.weight d)

omit [IsUltrametricDist B] in
include hφ hb in
theorem coefficientEvaluationTerm_norm_le (f : GeneralizedTateAlgebra r A)
    (d : σ →₀ ℕ) :
    ‖coefficientEvaluationTerm r φ b f d‖ ≤
      ‖MvPowerSeries.coeff d (series r A f)‖ * r.weight d := by
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hφ _) (hb d) (norm_nonneg _) (norm_nonneg _))

include hφ hb in
theorem norm_evaluateCoefficients_le (f : GeneralizedTateAlgebra r A) :
    ‖evaluateCoefficients r φ b f‖ ≤ ‖f‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg f)
    (fun d => (coefficientEvaluationTerm_norm_le r φ b hφ hb f d).trans
      (weighted_norm_coeff_le r A f d))

variable [CompleteSpace B]

include hφ hb in
theorem summable_coefficientEvaluationTerms (f : GeneralizedTateAlgebra r A) :
    Summable (coefficientEvaluationTerm r φ b f) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (coefficientEvaluationTerm_norm_le r φ b hφ hb f) f.property

include hφ hb in
theorem evaluateCoefficients_add (f g : GeneralizedTateAlgebra r A) :
    evaluateCoefficients r φ b (f + g) =
      evaluateCoefficients r φ b f + evaluateCoefficients r φ b g := by
  have ht : coefficientEvaluationTerm r φ b (f + g) =
      fun d => coefficientEvaluationTerm r φ b f d +
        coefficientEvaluationTerm r φ b g d := by
    funext d
    change φ.toAlgHom (MvPowerSeries.coeff d (f.val + g.val)) * _ = _
    rw [map_add, map_add, add_mul]
    rfl
  unfold evaluateCoefficients
  rw [ht]
  exact Summable.tsum_add (summable_coefficientEvaluationTerms r φ b hφ hb f)
    (summable_coefficientEvaluationTerms r φ b hφ hb g)

omit [CompleteSpace B] [IsUltrametricDist B] in
theorem evaluateCoefficients_monomial (d : σ →₀ ℕ) (a : A) :
    evaluateCoefficients r φ b (monomial r A d a) =
      φ a * StrictTateAlgebra.monomialValue σ B b d := by
  classical
  unfold evaluateCoefficients coefficientEvaluationTerm
  change (∑' e, φ.toAlgHom (MvPowerSeries.coeff e (MvPowerSeries.monomial d a)) *
    StrictTateAlgebra.monomialValue σ B b e) = _
  simp only [MvPowerSeries.coeff_monomial, apply_ite, map_zero, zero_mul, ite_mul,
    tsum_ite_eq]

omit [CompleteSpace B] [IsUltrametricDist B] in
@[simp] theorem evaluateCoefficients_constant (a : A) :
    evaluateCoefficients r φ b (constantAlgHom r K A a) = φ a := by
  have h : constantAlgHom r K A a = monomial r A 0 a := by
    apply Subtype.ext
    exact (MvPowerSeries.monomial_zero_eq_C_apply a).symm
  rw [h, evaluateCoefficients_monomial]
  simp [StrictTateAlgebra.monomialValue]

omit [CompleteSpace B] [IsUltrametricDist B] in
@[simp] theorem evaluateCoefficients_X (i : σ) :
    evaluateCoefficients r φ b (X r A i) = b i := by
  classical
  rw [X, evaluateCoefficients_monomial]
  rw [map_one, one_mul]
  simp [StrictTateAlgebra.monomialValue, Finsupp.prod_single_index]

include hφ hb in
theorem evaluateCoefficients_mul (f g : GeneralizedTateAlgebra r A) :
    evaluateCoefficients r φ b (f * g) =
      evaluateCoefficients r φ b f * evaluateCoefficients r φ b g := by
  classical
  let : NonarchimedeanRing B :=
    { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
  have hf := summable_coefficientEvaluationTerms r φ b hφ hb f
  have hg := summable_coefficientEvaluationTerms r φ b hφ hb g
  unfold evaluateCoefficients
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg (hf.mul_of_nonarchimedean hg)]
  apply tsum_congr
  intro d
  change φ.toAlgHom (MvPowerSeries.coeff d (f.val * g.val)) *
    StrictTateAlgebra.monomialValue σ B b d = _
  rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hm : StrictTateAlgebra.monomialValue σ B b (ij.1 + ij.2) =
      StrictTateAlgebra.monomialValue σ B b ij.1 *
        StrictTateAlgebra.monomialValue σ B b ij.2 :=
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  rw [map_mul, ← hsum, hm]
  exact mul_mul_mul_comm _ _ _ _

/-- The contractive evaluation homomorphism over an arbitrary normed coefficient algebra. -/
def evaluateCoefficientsHom : BoundedAlgHom K (GeneralizedTateAlgebra r A) B where
  toFun := evaluateCoefficients r φ b
  map_zero' := by
    simpa only [map_zero] using evaluateCoefficients_constant r φ b (0 : A)
  map_one' := by
    simpa only [map_one] using evaluateCoefficients_constant r φ b (1 : A)
  map_add' := evaluateCoefficients_add r φ b hφ hb
  map_mul' := evaluateCoefficients_mul r φ b hφ hb
  commutes' := by
    intro c
    have h : algebraMap K (GeneralizedTateAlgebra r A) c =
        constantAlgHom r K A (algebraMap K A c) :=
      IsScalarTower.algebraMap_apply K A (GeneralizedTateAlgebra r A) c
    rw [h, evaluateCoefficients_constant]
    exact φ.toAlgHom.commutes c
  bounded := ⟨1, zero_lt_one, fun f => by
    change ‖evaluateCoefficients r φ b f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_evaluateCoefficients_le r φ b hφ hb f⟩

/-- Relative monomials factor into their coefficient and coordinate product. -/
theorem relative_monomial_eq (d : σ →₀ ℕ) (a : A) :
    monomial r A d a = constantAlgHom r K A a *
      StrictTateAlgebra.monomialValue σ (GeneralizedTateAlgebra r A) (X r A) d := by
  apply Subtype.ext
  change MvPowerSeries.monomial d a =
    MvPowerSeries.C a * (weightedRestrictedSubalgebra r A).val
      (d.prod fun i n =>
        (⟨(X r A i).val, (X r A i).property⟩ : weightedRestrictedSubalgebra r A) ^ n)
  rw [map_finsuppProd]
  simp only [map_pow]
  exact MvPowerSeries.monomial_eq' d a

omit [CompleteSpace B] [IsUltrametricDist B] in
/-- A bounded relative algebra map is determined by coefficients and coordinates. -/
theorem relative_hom_ext
    (ψ χ : BoundedAlgHom K (GeneralizedTateAlgebra r A) B)
    (hconst : ∀ a, ψ (constantAlgHom r K A a) = χ (constantAlgHom r K A a))
    (hX : ∀ i, ψ (X r A i) = χ (X r A i)) : ψ = χ := by
  apply BoundedAlgHom.ext
  intro f
  have hmono : ∀ d a, ψ (monomial r A d a) = χ (monomial r A d a) := by
    intro d a
    rw [relative_monomial_eq (K := K)]
    change ψ.toAlgHom (_ * _) = χ.toAlgHom (_ * _)
    rw [map_mul, map_mul, hconst]
    congr 1
    unfold StrictTateAlgebra.monomialValue
    rw [map_finsuppProd, map_finsuppProd]
    simp only [map_pow, hX]
  have hψ := ψ.toContinuousLinearMap.map_tsum (hasSum_monomials r A f).summable
  have hχ := χ.toContinuousLinearMap.map_tsum (hasSum_monomials r A f).summable
  change ψ (∑' d, monomial r A d (MvPowerSeries.coeff d (series r A f))) = _ at hψ
  change χ (∑' d, monomial r A d (MvPowerSeries.coeff d (series r A f))) = _ at hχ
  rw [(hasSum_monomials r A f).tsum_eq] at hψ hχ
  exact hψ.trans ((tsum_congr fun d => hmono d _).trans hχ.symm)

end Langlands.Analytic.GeneralizedTateAlgebra
