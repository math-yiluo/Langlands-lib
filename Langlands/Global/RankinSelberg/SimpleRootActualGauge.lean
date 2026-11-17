import Langlands.Global.RankinSelberg.SimpleRootGaugeDescent
import Langlands.Global.RankinSelberg.UnfoldingWhittaker

/-! # Symmetric Schwartz data as a gauge on actual adelic points -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

open Langlands.GeneralLinear Unfolding

local instance actualGaugeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F] {r : ℕ}

private theorem continuous_of_mem_schwartzBruhat
    {Φ : RowVector F r → ℂ} (hΦ : Φ ∈ schwartzBruhat F r) : Continuous Φ := by
  have harch : Continuous (archimedeanCoordinates F r) := by
    apply continuous_pi
    intro i
    exact (continuous_infiniteAdeleCoordinates F).comp
      (continuous_fst.comp ((continuous_apply i).comp (continuous_apply 0)))
  have hfin : Continuous (finiteCoordinates F r) := by
    apply continuous_pi
    intro i
    exact continuous_snd.comp ((continuous_apply i).comp (continuous_apply 0))
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨Φinf, Φfin, hlc, -, rfl⟩ := h
    exact (Φinf.continuous.comp harch).mul (hlc.continuous.comp hfin)
  | zero => exact continuous_const
  | add Φ Ψ _ _ hΦ hΨ => exact hΦ.add hΨ
  | smul c Φ _ hΦ => exact hΦ.const_smul c

/-- Symmetric Schwartz data give a continuous exponent-zero gauge on the actual
adelic group, with the prescribed formula on every triangular-compact product. -/
theorem exists_actual_simpleRoot_gauge
    (c : F) (Φ : RowVector F r → ℂ) (hΦ : Φ ∈ schwartzBruhat F r)
    (hsymm : HasSimpleRootCoordinateSymmetries F c Φ) :
    ∃ Ξ : Points F (r + 1) → ℝ≥0∞, IsAdelicSimpleRootGauge F r 0 Ξ ∧
      (∀ (b : upperTriangularSubgroup (r + 1) (Adeles F))
        (k : PrimitiveAdelicHeight.standardCompact F (r + 1)),
        Ξ ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
          ((b : AdelicGL F (r + 1)) * k)) =
            ‖Φ (gaugeSimpleRootRow F r
              (triangularDiagonal (r + 1) (Adeles F) b))‖ₑ) ∧
      Continuous Ξ := by
  obtain ⟨Γ, hΓ, hformula, hleft, hright⟩ :=
    exists_continuous_simpleRoot_extension F c Φ
      (continuous_of_mem_schwartzBruhat F hΦ) hsymm
  let Ξ : Points F (r + 1) → ℝ≥0∞ :=
    fun g => ‖Γ (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)‖ₑ
  have hΞc : Continuous Ξ :=
    (hΓ.comp (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous).enorm
  have hΞformula
      (b : upperTriangularSubgroup (r + 1) (Adeles F))
      (k : PrimitiveAdelicHeight.standardCompact F (r + 1)) :
      Ξ ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        ((b : AdelicGL F (r + 1)) * k)) =
          ‖Φ (gaugeSimpleRootRow F r
            (triangularDiagonal (r + 1) (Adeles F) b))‖ₑ := by
    dsimp only [Ξ]
    rw [MulEquiv.apply_symm_apply, hformula]
  refine ⟨Ξ, ⟨le_refl 0, hΞc.measurable, ?_, ?_, Φ, hΦ, ?_⟩,
    hΞformula, hΞc⟩
  · intro n g
    let v : Langlands.GeneralLinear.upperUnipotent (r + 1) (Adeles F) :=
      ⟨GeneralLinearGroupPoints.adelicEquiv F (r + 1) n.val,
        (mem_unipotentAdelic_iff F n.val).mp n.property⟩
    dsimp only [Ξ]
    rw [map_mul]
    exact congrArg (fun z : ℂ => ‖z‖ₑ)
      (hleft v (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g))
  · intro k g
    let k' : PrimitiveAdelicHeight.standardCompact F (r + 1) :=
      ⟨GeneralLinearGroupPoints.adelicEquiv F (r + 1) k.val, k.property⟩
    dsimp only [Ξ]
    rw [map_mul]
    exact congrArg (fun z : ℂ => ‖z‖ₑ)
      (hright k' (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g))
  · intro d
    simp only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    let b : upperTriangularSubgroup (r + 1) (Adeles F) :=
      ⟨GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d,
        diagonalMatrixUnits_triangular d⟩
    simpa only [b, OneMemClass.coe_one, mul_one, triangularDiagonal_diagonal,
      gaugeDiagonalPoint] using hΞformula b 1

end Langlands.Global.RankinSelbergGlobal.GaugeDescent
