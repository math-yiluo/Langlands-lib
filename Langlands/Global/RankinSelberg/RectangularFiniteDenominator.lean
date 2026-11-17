import Langlands.Global.RankinSelberg.AdelicRectangularRootBounds
import Langlands.Global.RankinSelberg.EqualAnalyticDominated

/-! # A common finite denominator for rectangular coordinates -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa EqualAnalytic

variable (F : Type u) [Field F] [NumberField F]

/-- The finite-adelic coordinates of a rectangular adelic matrix. -/
def rectangleFiniteCoordinates (d a : ℕ)
    (x : Matrix (Fin d) (Fin a) (Adeles F)) :
    Matrix (Fin d) (Fin a) (FiniteAdeles F) :=
  fun i j => (x i j).2

/-- A common integral denominator for the simple-root row bounds each
finite root radius by the reciprocal of that denominator's local norm. -/
theorem finiteSimpleRootRadius_le_inverse_denominator
    {r : ℕ} (c : Fin (r + 1) → Ideles F) (q : 𝓞 F) (hq : q ≠ 0)
    (hroot : ∀ k : Fin r,
      algebraMap (𝓞 F) (FiniteAdeles F) q *
        ((c k.castSucc / c k.succ : Ideles F) : Adeles F).2 ∈ integralFiniteAdeles F)
    (v : FinitePlace F) :
    finiteSimpleRootRadius F r c v ≤
      ‖(algebraMap (𝓞 F) (FiniteAdeles F) q) v‖⁻¹ := by
  let D : FiniteCompletion F v := (algebraMap (𝓞 F) (FiniteAdeles F) q) v
  have hqF : (q : F) ≠ 0 := by exact_mod_cast hq
  have hD : D ≠ 0 := by
    change algebraMap F (FiniteCompletion F v) (q : F) ≠ 0
    exact (map_ne_zero (algebraMap F (FiniteCompletion F v))).mpr hqF
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hDle : ‖D‖ ≤ 1 := by
    have hh := (mem_integralFiniteAdeles F _).mp (algebraMap_ringOfIntegers_mem F q) v
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hh
  apply max_le
  · exact (one_le_inv₀ hDpos).mpr hDle
  · apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (norm_nonneg D))).mpr
    intro k
    have hh := (mem_integralFiniteAdeles F _).mp (hroot k) v
    change D * finiteProjection F v
      ((c k.castSucc / c k.succ : Ideles F) : Adeles F) ∈ v.adicCompletionIntegers F at hh
    have hn : ‖D‖ * ‖finiteProjection F v
        ((c k.castSucc / c k.succ : Ideles F) : Adeles F)‖ ≤ 1 := by
      rw [← norm_mul]
      simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        ← Valued.toNormedField.norm_le_one_iff] using hh
    rw [← one_div]
    apply (le_div_iff₀ hDpos).mpr
    simpa only [mul_comm] using hn

/-- Rectangular coordinates have one common finite denominator obtained
by a rank-dependent power of a denominator for the simple roots. -/
theorem rectangular_finite_denominator
    {a d : ℕ} (g : AdelicGL F a)
    (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 g x 1 = U * diagonalGL c * K)
    (q : 𝓞 F) (hq : q ≠ 0)
    (hroot : ∀ k : Fin (a + d),
      algebraMap (𝓞 F) (FiniteAdeles F) q *
        ((c k.castSucc / c k.succ : Ideles F) : Adeles F).2 ∈ integralFiniteAdeles F)
    (i : Fin d) (j : Fin a) :
    algebraMap (𝓞 F) (FiniteAdeles F) (q ^ (d * (d + 1))) *
      rectangleFiniteCoordinates F d a x i j ∈ integralFiniteAdeles F := by
  apply (mem_integralFiniteAdeles F _).mpr
  intro v
  let D : FiniteCompletion F v := (algebraMap (𝓞 F) (FiniteAdeles F) q) v
  have hqF : (q : F) ≠ 0 := by exact_mod_cast hq
  have hD : D ≠ 0 := by
    change algebraMap F (FiniteCompletion F v) (q : F) ≠ 0
    exact (map_ne_zero (algebraMap F (FiniteCompletion F v))).mpr hqF
  have hrad := finiteSimpleRootRadius_le_inverse_denominator F c q hq hroot v
  have hx := finiteProjection_rectangular_coordinate_le F g x U K c hU hK hfac v i j
  have hbound : ‖finiteProjection F v (x i j)‖ ≤ ‖D‖⁻¹ ^ (d * (d + 1)) := by
    exact hx.trans (pow_le_pow_left₀ (by
      exact le_trans zero_le_one (le_max_left _ _)) hrad _)
  have hnorm : ‖D ^ (d * (d + 1)) * finiteProjection F v (x i j)‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖D‖ ^ (d * (d + 1)) * (‖D‖⁻¹ ^ (d * (d + 1))) :=
        mul_le_mul_of_nonneg_left hbound (pow_nonneg (norm_nonneg _) _)
      _ = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD), one_pow]
  have hh : D ^ (d * (d + 1)) * finiteProjection F v (x i j) ∈
      v.adicCompletionIntegers F := by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hnorm
  rw [map_pow]
  change D ^ (d * (d + 1)) * finiteProjection F v (x i j) ∈ v.adicCompletionIntegers F
  exact hh

end Langlands.Global.RankinSelbergGlobal
