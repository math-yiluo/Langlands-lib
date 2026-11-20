import Langlands.Global.RankinSelberg.RealGodementLowerCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Real position principal series in the leading-exponent compact picture -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension RealJacquetFrobenius
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ

/-- Read the compact restriction of a position vector in a new position principal series. -/
def compactPictureExtension (ds : List RealBlock) (F : G → ℂ) : G → ℂ :=
  extension (shiftedExponent n (realPositionExponent ds)) (fun κ : K => F (Unitary.toUnits κ))

/-- The compact restriction is preserved by the compact-picture extension. -/
theorem compactPictureExtension_eqOn (ds : List RealBlock) (F : G → ℂ) :
    Set.EqOn (compactPictureExtension ds F) F (unitaryCompact ℝ n) := by
  intro k hk
  have hk' : Unitary.toUnits (⟨k.val, hk⟩ : K) = k := Units.ext rfl
  conv_lhs => rw [← hk']
  simpa only [compactPictureExtension, hk'] using
    extension_unitary (shiftedExponent n (realPositionExponent ds))
      (fun κ : K => F (Unitary.toUnits κ)) ⟨k.val, hk⟩

private theorem signDiagonal_toUnits (a : Fin n → ℝˣ) :
    Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) =
      Iwasawa.diagonalUnits (fun i => signUnit (a i)) := by
  apply Units.ext
  change (Matrix.diagonal (fun i => signReal (a i : ℝ)) : M) =
    Matrix.diagonal (fun i => (signUnit (a i) : ℝ))
  simp only [signUnit_val]

theorem compactPictureExtension_mem_principalSeries {ds es : List RealBlock} {F : G → ℂ}
    (hF : F ∈ principalSeries ℝ n (realPositionCharacter ds))
    (hSign : ∀ i (x : ℝˣ), realPositionCharacter es i (signUnit x) =
      realPositionCharacter ds i (signUnit x)) :
    compactPictureExtension es F ∈ principalSeries ℝ n (realPositionCharacter es) := by
  let s := shiftedExponent n (realPositionExponent es)
  refine ⟨?_, ?_⟩
  · apply contMDiff_of_contDiffOn
      (ψ := fun x : M => gramExpression s 1 (complexify x) * unitsExtension F (signedOrthogonal x))
    · apply (contDiffOn_gramExpression s 1).mul
      refine (contDiffOn_unitsExtension hF.1).comp contDiffOn_signedOrthogonal ?_
      intro x hx
      rw [← hx.unit_spec]
      exact (Unitary.toUnits (signedOrthogonalPart hx.unit)).isUnit
    · intro g
      have he := unitsExtension_val F (Unitary.toUnits (signedOrthogonalPart g))
      change _ = gramExpression s 1 (complexify g.val) * unitsExtension F (signedOrthogonal g.val)
      rw [show signedOrthogonal g.val = (Unitary.toUnits (signedOrthogonalPart g)).val from rfl, he]
      rfl
  · apply extension_mul_left (realPositionExponent es) (realPositionCharacter_eq_signUnit_mul es)
    intro a κ
    have hc : principalSeriesCharacter ℝ n (realPositionCharacter es) (fun i => signUnit (a i)) =
        principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) := by
      unfold principalSeriesCharacter
      exact Finset.prod_congr rfl fun i _ => by rw [hSign i (a i)]
    change F (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
      principalSeriesCharacter ℝ n (realPositionCharacter es) (fun i => signUnit (a i)) *
        F (Unitary.toUnits κ)
    rw [map_mul, signDiagonal_toUnits, hc]
    simpa only [Subgroup.coe_one, mul_one] using
      hF.2 (fun i => signUnit (a i)) (1 : GeneralLinear.upperUnipotent n ℝ) (Unitary.toUnits κ)

/-- Vary the leading inducing exponent while holding the compact restriction fixed. -/
def leadingCompactVector (p : Fin 2) (ds : List RealBlock) (F : G → ℂ) (z : ℂ) : G → ℂ :=
  compactPictureExtension (.character (charData p z) :: ds) F

theorem leadingCompactVector_mem_principalSeries (p : Fin 2) (ds : List RealBlock)
    {F : G → ℂ} {w : ℂ}
    (hF : F ∈ principalSeries ℝ n (realPositionCharacter (.character (charData p w) :: ds))) (z : ℂ) :
    leadingCompactVector p ds F z ∈ principalSeries ℝ n
      (realPositionCharacter (.character (charData p z) :: ds)) := by
  apply compactPictureExtension_mem_principalSeries hF
  intro i x
  cases i with
  | zero =>
    change charFun p z (signUnit x : ℝ) = charFun p w (signUnit x : ℝ)
    simp only [charFun, abs_signUnit, Complex.ofReal_one, Complex.one_cpow, mul_one]
  | succ _ => rfl

theorem differentiable_leadingCompactVector (p : Fin 2) (ds : List RealBlock)
    (F : G → ℂ) (g : G) : Differentiable ℂ (fun z => leadingCompactVector p ds F z g) := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  let b : M := Matrix.diagonal (fun i => (a i : ℝ)) * u.val.val
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a u
  have hDiag (i : Fin n) : b i i = a i := diagonal_mul_apply_self a u i
  have hNonzero (i : Fin n) : b i i ≠ 0 := by rw [hDiag]; exact (a i).ne_zero
  have hx : (Iwasawa.diagonalUnits a * u.val * k).val = b * k.val := rfl
  simp only [leadingCompactVector, compactPictureExtension, extension_eq _ _ hb hNonzero hk hx]
  apply Differentiable.mul_const
  apply Differentiable.fun_finsetProd
  intro i _
  let x : ℂ := ((|b i i| : ℝ) : ℂ)
  let : NeZero x := ⟨Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (hNonzero i))⟩
  apply (differentiable_const_cpow_of_neZero x).comp
  change Differentiable ℂ (fun z => realPositionExponent (.character (charData p z) :: ds) i.val +
    (((n : ℂ) - 1) / 2 - (i.val : ℂ)))
  apply Differentiable.add_const
  cases i.val with
  | zero => exact differentiable_id
  | succ j => exact differentiable_const _

/-- The smooth real position principal series has a fixed compact picture as
one inducing exponent varies with fixed parity, with entire evaluation on the group. -/
def RealGodementCompactPictureStatement : Prop :=
  ∀ (n : ℕ) (p : Fin 2) (ds : List RealBlock) (w : ℂ)
    (F : Langlands.GeneralLinear n ℝ → ℂ),
    F ∈ principalSeries ℝ n (realPositionCharacter (.character (charData p w) :: ds)) →
    (∀ z : ℂ,
      leadingCompactVector p ds F z ∈ principalSeries ℝ n
        (realPositionCharacter (.character (charData p z) :: ds)) ∧
      Set.EqOn (leadingCompactVector p ds F z) F (unitaryCompact ℝ n)) ∧
    ∀ g, Differentiable ℂ (fun z => leadingCompactVector p ds F z g)

theorem realGodementCompactPicture : RealGodementCompactPictureStatement := by
  intro n p ds w F hF
  exact ⟨fun z => ⟨leadingCompactVector_mem_principalSeries p ds hF z,
    compactPictureExtension_eqOn _ F⟩, differentiable_leadingCompactVector p ds F⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
