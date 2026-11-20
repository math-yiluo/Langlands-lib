import Langlands.Representation.Archimedean.RealLeviBump
import Langlands.Representation.Archimedean.RealLeviCompactChart

/-! # Localization of compact Levi chart coordinates -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealLeviCompactChart

open Langlands.GeneralLinear GramFormula PrincipalSeriesExtension
  RealSignedOrthogonalDifferential RealLeviBump
  RealLeviChart RealLeviParabolicIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {c : ℕ} (sz : Fin c → ℕ)

local notation "N" => ∑ i, sz i
local notation "K" => Matrix.unitaryGroup (Fin N) ℝ
local notation "M" => Matrix (Fin N) (Fin N) ℝ

/-- The compact block diagonal factor of the Levi chart. -/
def blockFrame : LeviFrame sz →* K where
  toFun κ := ⟨(bd κ : M), blockDiagGL_mem_unitaryCompact κ⟩
  map_one' := Subtype.ext (congrArg Units.val (map_one (blockDiagGL sz)))
  map_mul' κ ρ := Subtype.ext (congrArg (fun x : RealLeviBlockHaar.Kc (cls sz) =>
    ((x.val : Langlands.GeneralLinear N ℝ) : M)) (map_mul (bdK (sz := sz)) κ ρ))

@[simp]
theorem toUnits_blockFrame (k : LeviFrame sz) : Unitary.toUnits (blockFrame sz k) = bd k :=
  Units.ext rfl

theorem continuous_blockFrame : Continuous (blockFrame sz) :=
  continuous_bd_val.subtype_mk _

theorem blockZero_blockFrame (k : LeviFrame sz) : BlockZero sz (blockFrame sz k : M) :=
  (blockDiagGL_mem_blockOrth k).2

theorem mem_range_blockFrame_iff (k : K) : k ∈ range (blockFrame sz) ↔ BlockZero sz (k : M) := by
  constructor
  · rintro ⟨κ, rfl⟩
    exact blockZero_blockFrame sz κ
  · intro hk
    obtain ⟨κ, hκ⟩ := exists_blockDiagGL_eq
      (mem_blockOrth_of_mem_unitaryCompact (sz := sz) (g := Unitary.toUnits k) k.2 hk)
    exact ⟨κ, Subtype.ext (congrArg Units.val hκ)⟩

theorem compactFrame_eq_mul_blockFrame (k : LeviFrame sz) (X : Coord sz → ℝ) :
    compactFrame sz k X = signedOrthogonalPart (lowerGL sz X) * blockFrame sz k := by
  rw [compactFrame, ← toUnits_blockFrame sz k, orthogonalPart_mul_right]

@[simp]
theorem compactFrame_zero (k : LeviFrame sz) : compactFrame sz k 0 = blockFrame sz k := by
  rw [compactFrame_eq_mul_blockFrame, RealLeviLimit.lowerGL_zero]
  have h1 : signedOrthogonalPart (1 : Langlands.GeneralLinear N ℝ) = 1 := by
    apply Subtype.ext
    change signedOrthogonal (1 : M) = 1
    simpa [signReal] using signedOrthogonal_mul (b := (1 : M)) (κ := (1 : M))
      Matrix.blockTriangular_one (fun _ => by simp) (by simp)
  rw [h1, one_mul]

/-- The continuous trailing-minor function on the compact group. -/
def frameBump (k : K) : ℝ :=
  ∏ i : Fin c, (padded (start sz (i : ℕ)) (k : M)).det ^ 2

theorem continuous_frameBump : Continuous (frameBump sz) := by
  apply continuous_finsetProd
  intro i _
  apply Continuous.pow _ _
  apply Continuous.matrix_det
  apply continuous_matrix
  intro p q
  by_cases h : start sz (i : ℕ) ≤ (p : ℕ) ∧ start sz (i : ℕ) ≤ (q : ℕ)
  · simp only [padded, Matrix.of_apply, ite_eq_left h]
    exact continuous_subtype_val.matrix_elem p q
  · simp only [padded, Matrix.of_apply, ite_eq_right h]
    exact continuous_const

private theorem mul_transpose_eq_one (k : K) : (k : M) * (k : M)ᵀ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.mem_unitaryGroup_iff.mp k.2

theorem frameBump_eq_omega (k : K) : frameBump sz k = omega sz (k : M) :=
  (omega_of_orth sz (mul_transpose_eq_one sz k)).symm

theorem frameBump_eq_one_of_blockZero {k : K} (hk : BlockZero sz (k : M)) :
    frameBump sz k = 1 := by
  unfold frameBump
  exact Finset.prod_eq_one fun i _ =>
    det_padded_sq _ (mul_transpose_eq_one sz k) (blockUpper_of_blockZero sz hk i)

/-- The compact trailing-minor function pulls back to the opposite-unipotent bump. -/
theorem frameBump_compactFrame (k : LeviFrame sz) (X : Coord sz → ℝ) :
    frameBump sz (compactFrame sz k X) = beta sz X := by
  let x := lowerGL sz X * bd k
  let Q : K := compactFrame sz k X
  let B : M := (x : M) * (Q : M)ᵀ
  have hB : B.IsUpperTriangular := mul_transpose_signedOrthogonal_upper x.isUnit
  have hBunit : IsUnit B := x.isUnit.mul (isUnit_iff_exists_inv.mpr ⟨(Q : M),
    mul_eq_one_comm.mp (mul_transpose_eq_one sz Q)⟩)
  have hdiag (i : Fin N) : B i i ≠ 0 := by
    have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det B).mp hBunit)
    rw [Matrix.det_of_isUpperTriangular hB] at hd
    exact fun h => hd (Finset.prod_eq_zero (Finset.mem_univ i) h)
  have hBQ : B * (Q : M) = (x : M) := by
    change (x : M) * (Q : M)ᵀ * (Q : M) = _
    rw [mul_assoc, mul_eq_one_comm.mp (mul_transpose_eq_one sz Q), mul_one]
  calc
    frameBump sz Q = omega sz (Q : M) := frameBump_eq_omega sz Q
    _ = omega sz (x : M) := by rw [← hBQ, omega_mul_upper sz hB hdiag]
    _ = beta sz X := by
      change omega sz ((lowerGL sz X : M) * (bd k : M)) = _
      rw [lowerGL_val, omega_mul_right sz _ (blockDiagGL_mem_blockOrth k).1
        (blockDiagGL_mem_blockOrth k).2]
      rfl

/-- Frames near the compact block subgroup have uniformly small lower block coordinates. -/
def RealLeviCompactChartSupportStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ) (δ : ℝ), 0 < δ →
    ∃ U : Set (Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ), IsOpen U ∧
      range (blockFrame sz) ⊆ U ∧
      ∀ (k : LeviFrame sz) (X : Coord sz → ℝ), compactFrame sz k X ∈ U → ‖X‖ < δ

theorem realLeviCompactChartSupport : RealLeviCompactChartSupportStatement := by
  intro c sz δ hδ
  obtain ⟨q, hq, hgap⟩ := exists_gap (sz := sz) hδ
  let U := {k | q < frameBump sz k}
  refine ⟨U, isOpen_lt continuous_const (continuous_frameBump sz), ?_, ?_⟩
  · intro k hk
    change q < frameBump sz k
    rw [frameBump_eq_one_of_blockZero sz ((mem_range_blockFrame_iff sz k).mp hk)]
    exact hq
  · intro k X hX
    change q < frameBump sz (compactFrame sz k X) at hX
    rw [frameBump_compactFrame sz] at hX
    exact lt_of_not_ge fun h => (not_lt_of_ge (hgap X h)) hX

end Langlands.Archimedean.RealLeviCompactChart
