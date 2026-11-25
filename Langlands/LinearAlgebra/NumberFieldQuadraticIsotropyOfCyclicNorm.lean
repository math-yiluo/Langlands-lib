import Langlands.LinearAlgebra.QuadraticFourDimensionalDescent
import Langlands.LinearAlgebra.QuadraticIsotropyLowRank

/-! # Local-to-global quadratic isotropy from cyclic Hasse norm -/

noncomputable section

universe u

open NumberField QuadraticMap
open scoped BigOperators

namespace Langlands

open ClassFieldTheory.Global

/-- Cyclic Hasse norm implies local-to-global quadratic isotropy over number fields. -/
def NumberFieldQuadraticIsotropyOfCyclicNormStatement : Prop :=
  CyclicHasseNormStatement.{u} → NumberFieldQuadraticIsotropyStatement.{u}

namespace QuadraticIsotropy

private theorem isotropic_fin_four_iff_norm {K : Type*} [Field K] [CharZero K]
    (w : Fin 4 → K) (hw : ∀ i, w i ≠ 0) (hdisc : IsSquare (∏ i, w i)) :
    ¬ (weightedSumSquares K w).Anisotropic ↔
      ∃ x y : K, x ^ 2 - (-w 1 / w 0) * y ^ 2 = -w 2 / w 0 := by
  obtain ⟨s, hs⟩ := hdisc.exists_sq
  have hs₀ : s ≠ 0 := by
    intro h
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)) (by simpa [h] using hs)
  let a := -w 1 / w 0
  let b := -w 2 / w 0
  let t := s / (w 1 * w 2)
  have ht : t ≠ 0 := div_ne_zero hs₀ (mul_ne_zero (hw 1) (hw 2))
  have hscale : w 3 = w 0 * (a * b * t ^ 2) := by
    dsimp only [a, b, t]
    rw [div_pow, ← hs, Fin.prod_univ_four]
    field_simp [hw 0, hw 1, hw 2]
  have eval (z : Fin 4 → K) : weightedSumSquares K w z =
      w 0 * (z 0 ^ 2 - a * z 1 ^ 2 - b * (z 2 ^ 2 - a * (t * z 3) ^ 2)) := by
    simp only [weightedSumSquares_apply, smul_eq_mul, ← pow_two, Fin.sum_univ_four]
    rw [hscale]
    dsimp only [a, b]
    field_simp [hw 0]
    ring
  constructor
  · intro h
    obtain ⟨z, hz, hq⟩ := (not_anisotropic_iff_exists _).mp h
    have hne : z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ t * z 3 ≠ 0 := by
      by_contra! hn
      apply hz
      funext i
      fin_cases i
      · exact hn.1
      · exact hn.2.1
      · exact hn.2.2.1
      · exact (mul_eq_zero.mp hn.2.2.2).resolve_left ht
    rw [eval] at hq
    exact QuadraticFourDimensionalDescent.exists_eq_of_four_zero
      (div_ne_zero (neg_ne_zero.mpr (hw 1)) (hw 0)) hne
      (sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (hw 0)))
  · rintro ⟨x, y, he⟩
    change x ^ 2 - a * y ^ 2 = b at he
    refine (not_anisotropic_iff_exists _).mpr ⟨![x, y, 1, 0], ?_, ?_⟩
    · intro h
      exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h (2 : Fin 4))
    · rw [eval]
      simp [he]

private theorem exists_local_norm_four {F : Type u} [Field F] [NumberField F]
    {A : Type*} [Field A] [Algebra F A]
    (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0) (hdisc : IsSquare (∏ i, w i))
    (h : ¬ (weightedSumSquares A (fun i => algebraMap F A (w i))).Anisotropic) :
    ∃ x y : A, x ^ 2 - algebraMap F A (-w 1 / w 0) * y ^ 2 = algebraMap F A (-w 2 / w 0) := by
  let : CharZero A := Algebra.charZero_of_charZero F A
  have hdiscA : IsSquare (∏ i, algebraMap F A (w i)) := by
    rw [← map_prod (algebraMap F A)]
    exact hdisc.map _
  have hnorm := (isotropic_fin_four_iff_norm _ (fun i => (map_ne_zero _).2 (hw i)) hdiscA).mp h
  simpa only [map_div₀, map_neg] using hnorm

private theorem isotropic_fin_four_of_square_discriminant
    (norm : QuadraticNormLocalGlobalStatement.{u}) {F : Type u} [Field F] [NumberField F]
    (w : Fin 4 → F) (hw : ∀ i, w i ≠ 0) (hdisc : IsSquare (∏ i, w i))
    (h : DiagonalLocallyIsotropic F w) : ¬ (weightedSumSquares F w).Anisotropic := by
  apply (isotropic_fin_four_iff_norm w hw hdisc).mpr
  exact norm (div_ne_zero (neg_ne_zero.mpr (hw 1)) (hw 0))
    (div_ne_zero (neg_ne_zero.mpr (hw 2)) (hw 0))
    (fun q => exists_local_norm_four w hw hdisc (h (.inr q)))
    (fun p => exists_local_norm_four w hw hdisc (h (.inl p)))

/-- In rank four, solve the norm equation over the field if the discriminant is
square. Otherwise solve it over the quadratic discriminant extension and descend. -/
theorem isotropic_fin_four_of_norm (norm : QuadraticNormLocalGlobalStatement.{u}) :
    NumberFieldDiagonalRankFourIsotropyStatement.{u} := by
  intro F _ _ w hw h
  let d := ∏ i, w i
  by_cases hdisc : IsSquare d
  · exact isotropic_fin_four_of_square_discriminant norm w hw hdisc h
  let : Fact (¬ IsSquare d) := ⟨hdisc⟩
  let E := QuadraticAlgebra F d 0
  let : Algebra.IsQuadraticExtension F E := ⟨QuadraticNormEquation.finrank_quadraticAlgebra d⟩
  let : NumberField E := NumberField.of_module_finite F E
  let wE : Fin 4 → E := fun i => algebraMap F E (w i)
  have hdiscE : IsSquare (∏ i, wE i) := by
    change IsSquare (∏ i, algebraMap F E (w i))
    rw [← map_prod (algebraMap F E)]
    exact (isSquare_iff_exists_sq _).mpr
      ⟨QuadraticAlgebra.omega, (QuadraticNormEquation.omega_sq d).symm⟩
  have hisoE := isotropic_fin_four_of_square_discriminant norm wE
    (fun i => (map_ne_zero _).2 (hw i)) hdiscE (locallyIsotropic_map E h)
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  exact QuadraticFourDimensionalDescent.diagonal_not_anisotropic_of_discriminant_extension rfl
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)) hisoE

end QuadraticIsotropy

/-- Cyclic Hasse norm gives isotropy in low ranks, and weak approximation then gives
isotropy in all ranks. -/
theorem numberFieldQuadraticIsotropy_of_cyclicNorm :
    NumberFieldQuadraticIsotropyOfCyclicNormStatement.{u} := by
  intro hasseNorm
  let norm : QuadraticNormLocalGlobalStatement.{u} :=
    QuadraticNormLocalGlobal.exists_eq_of_local hasseNorm
  exact numberFieldQuadraticIsotropy_of_diagonal
    (QuadraticIsotropy.diagonalIsotropy_of_norm_and_rankFour norm
      (QuadraticIsotropy.isotropic_fin_four_of_norm norm))

end Langlands
