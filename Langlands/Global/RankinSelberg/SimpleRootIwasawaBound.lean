import Langlands.Global.RankinSelberg.SimpleRootGaugeDescent

/-! # Transport of diagonal Whittaker bounds through adelic Iwasawa factors -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear Unfolding
open Langlands.Automorphic.CuspidalWhittaker

local instance iwasawaBoundSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The triangular factorization with its diagonal removed, in matrix coordinates. -/
theorem exists_matrix_unipotent_diagonal_standardCompact (n : ℕ) (g : AdelicGL F n) :
    ∃ (d : Fin n → Ideles F) (k : PrimitiveAdelicHeight.standardCompact F n)
      (v : Langlands.GeneralLinear.upperUnipotent n (Adeles F)),
      g = (v : AdelicGL F n) * (diagonalMatrixUnits (Adeles F) d * (k : AdelicGL F n)) := by
  obtain ⟨⟨b, k⟩, hg⟩ := standardCompact_factor_surjective F n g
  refine ⟨triangularDiagonal n (Adeles F) b, k, triangularUnipotent b, ?_⟩
  rw [← mul_assoc, triangularUnipotent_mul_diagonal]
  exact hg.symm

theorem adelicEquiv_symm_mem_gaugeStandardCompact (n : ℕ)
    (k : PrimitiveAdelicHeight.standardCompact F n) :
    (GeneralLinearGroupPoints.adelicEquiv F n).symm (k : AdelicGL F n) ∈
      gaugeStandardCompact F n := by
  change (GeneralLinearGroupPoints.adelicEquiv F n)
    ((GeneralLinearGroupPoints.adelicEquiv F n).symm (k : AdelicGL F n)) ∈
      PrimitiveAdelicHeight.standardCompact F n
  simpa only [MulEquiv.apply_symm_apply] using k.property

theorem adelicEquiv_symm_mem_unipotentAdelic (n : ℕ)
    (v : Langlands.GeneralLinear.upperUnipotent n (Adeles F)) :
    (GeneralLinearGroupPoints.adelicEquiv F n).symm (v : AdelicGL F n) ∈
      unipotentAdelic F n := by
  rw [mem_unipotentAdelic_iff]
  rw [MulEquiv.apply_symm_apply]
  exact v.property

/-- Actual adelic points factor into a full unipotent point, an idelic diagonal,
and a point of the standard compact subgroup. -/
theorem exists_unipotent_diagonal_standardCompact (n : ℕ) (g : Points F n) :
    ∃ (d : Fin n → Ideles F) (k : gaugeStandardCompact F n)
      (v : unipotentAdelic F n),
      g = (v : Points F n) * (gaugeDiagonalPoint F n d * (k : Points F n)) := by
  let E := GeneralLinearGroupPoints.adelicEquiv F n
  obtain ⟨d, k, v, hg⟩ := exists_matrix_unipotent_diagonal_standardCompact F n (E g)
  refine ⟨d, ⟨E.symm k, adelicEquiv_symm_mem_gaugeStandardCompact F n k⟩,
    ⟨E.symm v, adelicEquiv_symm_mem_unipotentAdelic F n v⟩, ?_⟩
  have h := congrArg E.symm hg
  simpa only [MulEquiv.symm_apply_apply, map_mul, E, gaugeDiagonalPoint] using h

/-- Whittaker norms are invariant under the full adelic unipotent subgroup. -/
theorem norm_whittaker_unipotent_mul {r : ℕ}
    {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}
    (hV : WhittakerDecayClass F r V R)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (f : V) (v : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    ‖whittaker F r ψ f ((v : Points F (r + 1)) * g)‖ =
      ‖whittaker F r ψ f g‖ := by
  rw [whittaker_mul_left F (r := r) ψ hψ
    (f : Points F (r + 1) → ℂ) (hV.rational f) v g, norm_mul,
    norm_genericCharacter F r ψ hψ.2.2.2, one_mul]

/-- A diagonal bound uniform over the standard compact subgroup gives the
same bound on the full group for an invariant extension of its root profile. -/
theorem whittaker_le_of_simpleRoot_diagonal_bound {r : ℕ}
    {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}
    (hV : WhittakerDecayClass F r V R) (β : ℝ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (f : V) (Φ : RowVector F r → ℂ)
    (Ξ : Points F (r + 1) → ℝ≥0∞)
    (hN : ∀ (v : unipotentAdelic F (r + 1)) (g : Points F (r + 1)),
      Ξ ((v : Points F (r + 1)) * g) = Ξ g)
    (hK : ∀ (k : gaugeStandardCompact F (r + 1)) (g : Points F (r + 1)),
      Ξ (g * (k : Points F (r + 1))) = Ξ g)
    (hdiag : ∀ d : Fin (r + 1) → Ideles F,
      Ξ (gaugeDiagonalPoint F (r + 1) d) = ‖Φ (gaugeSimpleRootRow F r d)‖ₑ)
    (hbound : ∀ (d : Fin (r + 1) → Ideles F) (k : gaugeStandardCompact F (r + 1)),
      ‖whittaker F r ψ f (gaugeDiagonalPoint F (r + 1) d * (k : Points F (r + 1)))‖ ≤
        detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d * (k : Points F (r + 1))) ^ β *
          ‖Φ (gaugeSimpleRootRow F r d)‖)
    (g : Points F (r + 1)) :
    ‖whittaker F r ψ f g‖ₑ ≤
      ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g := by
  obtain ⟨d, k, v, rfl⟩ := exists_unipotent_diagonal_standardCompact F (r + 1) g
  rw [hN, hK, hdiag]
  rw [← ofReal_norm, norm_whittaker_unipotent_mul F hV ψ hψ f,
    detNorm_mul, detNorm_unipotent, one_mul, ← ofReal_norm]
  rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (detNorm_pos F _ _) β).le]
  exact ENNReal.ofReal_le_ofReal (hbound d k)

end Langlands.Global.RankinSelbergGlobal.GaugeDescent
