import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugePadding
import Langlands.Global.RankinSelberg.StandardCompactPadding
import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.AdelicGLSiegelShape

/-! # Compact factors in padded simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance gaugeCompactPaddingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- On group-scheme points, padding preserves the standard compact subgroup. -/
theorem pad_mem_gaugeStandardCompact {m n : ℕ} (h : m ≤ n)
    (g : gaugeStandardCompact F m) :
    pad F h (g : Points F m) ∈ gaugeStandardCompact F n := by
  change GeneralLinearGroupPoints.adelicEquiv F n (pad F h (g : Points F m)) ∈
    PrimitiveAdelicHeight.standardCompact F n
  rw [adelicEquiv_pad]
  exact padGL_mem_standardCompact F h _ g.property

/-- Every adelic point has unipotent, diagonal-idele and standard compact factors. -/
theorem exists_gaugeIwasawa (m : ℕ) (g : Points F m) :
    ∃ (x : unipotentAdelic F m) (d : Fin m → Ideles F) (k : gaugeStandardCompact F m),
      g = (x : Points F m) * gaugeDiagonalPoint F m d * (k : Points F m) := by
  obtain ⟨β, κ, hg, hβ, hκ⟩ :=
    PrimitiveAdelicHeight.exists_isStandardIwasawaFactorization F m
      (GeneralLinearGroupPoints.adelicEquiv F m g)
  have hβ' : β.val.IsUpperTriangular :=
    (GeneralLinear.mem_upperTriangularSubgroup_iff _).mp hβ
  let d : Fin m → Ideles F := PrimitiveAdelicHeight.diagonalUnit β hβ'
  let a := GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d
  let ν := β * a⁻¹
  have hν : PrimitiveAdelicHeight.IsUnitriangular ν.val := by
    change PrimitiveAdelicHeight.IsUnitriangular (β.val * a⁻¹.val)
    have ha : a⁻¹.val =
        Matrix.diagonal (fun i => (((d i)⁻¹ : Ideles F) : Adeles F)) := by
      change (GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d)⁻¹.val = _
      rw [← map_inv, GroupScheme.GeneralLinear.diagonalMatrixUnits_val]
      rfl
    rw [ha]
    exact PrimitiveAdelicHeight.isUnitriangular_mul_diagonal hβ' d (fun _ => rfl)
  let x : unipotentAdelic F m :=
    ⟨(GeneralLinearGroupPoints.adelicEquiv F m).symm ν,
      (mem_unipotentAdelic_iff F _).mpr (by simpa using hν)⟩
  let k : gaugeStandardCompact F m :=
    ⟨(GeneralLinearGroupPoints.adelicEquiv F m).symm κ, by
      change GeneralLinearGroupPoints.adelicEquiv F m
        ((GeneralLinearGroupPoints.adelicEquiv F m).symm κ) ∈
          PrimitiveAdelicHeight.standardCompact F m
      simpa using hκ⟩
  refine ⟨x, d, k, ?_⟩
  apply (GeneralLinearGroupPoints.adelicEquiv F m).injective
  simp only [map_mul, x, k, gaugeDiagonalPoint, MulEquiv.apply_symm_apply]
  change GeneralLinearGroupPoints.adelicEquiv F m g = (β * a⁻¹) * a * κ
  rw [inv_mul_cancel_right, hg]

/-- A padded gauge is given in Iwasawa coordinates by its Schwartz function
and the negative power of the first diagonal norm. -/
theorem IsAdelicSimpleRootGauge.exists_padded_formula
    {r t : ℕ} (h : t < r) {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ) :
    ∃ Φ : RowVector F r → ℂ, Φ ∈ schwartzBruhat F r ∧
      ∀ (x : unipotentAdelic F (t + 1)) (d : Fin (t + 1) → Ideles F)
        (k : gaugeStandardCompact F (t + 1)),
        Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
          ((x : Points F (t + 1)) * gaugeDiagonalPoint F (t + 1) d *
            (k : Points F (t + 1)))) =
          ENNReal.ofReal
            (((IdeleAbsoluteValue.full F (d 0) : ℝ≥0) : ℝ) ^ (-τ)) *
              ‖Φ (gaugeSimpleRootRow F r (gaugePaddedIdeles F d))‖ₑ := by
  obtain ⟨-, -, hN, hK, Φ, hΦ, hdiag⟩ := hΞ
  refine ⟨Φ, hΦ, fun x d k => ?_⟩
  let hm := Nat.le_of_lt (Nat.succ_lt_succ h)
  rw [pad_mul, pad_mul]
  rw [hK ⟨pad F hm (k : Points F (t + 1)), pad_mem_gaugeStandardCompact F hm k⟩]
  have hx := hN (padUnipotent F hm x) (pad F hm (gaugeDiagonalPoint F (t + 1) d))
  change Ξ (pad F hm (x : Points F (t + 1)) *
    pad F hm (gaugeDiagonalPoint F (t + 1) d)) =
      Ξ (pad F hm (gaugeDiagonalPoint F (t + 1) d)) at hx
  rw [hx, pad_gaugeDiagonalPoint, hdiag,
    gaugeSimpleRootNormProduct_padded F h]

end Langlands.Global.RankinSelbergGlobal
