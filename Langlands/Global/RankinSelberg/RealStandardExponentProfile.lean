import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Global.RankinSelberg.RealStandardCompactBanachAction

/-! # Exponent changes in the compact profile of a real standard action -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "I" => matrixModel ℝ n
local notation "Cₖ" => C(K, ℂ)

private def gramLog (a : Fin n → ℂ) (y : M) : ℂ :=
  ∑ l : Fin n, a l * ((↑(Real.log (gram l.val y)) - ↑(Real.log (gram (l.val + 1) y))) / 2)

private theorem contDiffOn_gramLog (a : Fin n → ℂ) :
    ContDiffOn ℝ ∞ (gramLog a) {y : M | IsUnit y} := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  have hlog (i : ℕ) :
      ContDiffAt ℝ ∞ (fun x : M => (↑(Real.log (gram i x)) : ℂ)) y := by
    have hp := gram_pos hy.unit i
    rw [IsUnit.unit_spec] at hp
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp y
      ((contDiff_gram i).contDiffAt.log hp.ne')
  unfold gramLog
  refine ContDiffAt.sum fun l _ => contDiffAt_const.mul ?_
  exact ((hlog l.val).sub (hlog (l.val + 1))).div_const 2

private theorem contMDiff_gramLog (a : Fin n → ℂ) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : G => gramLog a (g : M)) :=
  (contDiffOn_gramLog a).contMDiffOn.comp_contMDiff (Units.contMDiff_val (n := ∞))
    fun g => g.isUnit

/-- On each compact orbit, the exponent shift is measured by the logarithms of
successive Gram determinants. -/
def exponentLogProfile (a : Fin n → ℂ) (g : G) : Cₖ :=
  ⟨fun k => gramLog a (Unitary.toUnits k * g : G).val,
    (contMDiff_gramLog a).continuous.comp (continuous_unitary_toUnits.mul continuous_const)⟩

theorem contMDiff_exponentLogProfile (a : Fin n → ℂ) :
    ContMDiff I 𝓘(ℝ, Cₖ) ∞ (exponentLogProfile a) := by
  classical
  let U : Set M := {y | IsUnit y}
  have hU : IsOpen U := isOpen_setOf_isUnit_matrix
  let j : C(K, M) :=
    ⟨fun k => (Unitary.toUnits k : G).val, Units.continuous_val.comp continuous_unitary_toUnits⟩
  have hj (k : K) : j k ∈ U := (Unitary.toUnits k : G).isUnit
  let H (p : M × M) := gramLog a (p.2 * p.1)
  have hH : ContDiffOn ℝ ∞ H (U ×ˢ U) :=
    (contDiffOn_gramLog a).comp (contDiff_snd.mul contDiff_fst).contDiffOn
      (fun _ hp => hp.2.mul hp.1)
  let F (y : M) : Cₖ := if hy : y ∈ U then
    ⟨fun k => H (y, j k), hH.continuousOn.comp_continuous
      (continuous_const.prodMk j.continuous) (fun k => ⟨hy, hj k⟩)⟩
    else 0
  have hF (y : M) (hy : y ∈ U) (k : K) : F y k = H (y, j k) := by simp [F, hy]
  have h := Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint j hU hU hj hH hF
  refine (h.contMDiffOn.comp_contMDiff (Units.contMDiff_val (n := ∞)) fun g : G => g.isUnit).congr ?_
  intro g
  exact ContinuousMap.ext fun k => (hF g.val g.isUnit k).symm

private theorem gramExpression_one_eq_exp (s : Fin n → ℂ) (g : G) :
    gramExpression s 1 (complexify (g : M)) = Complex.exp (gramLog s (g : M)) := by
  unfold gramExpression gramLog
  rw [map_one, mul_one, Complex.exp_sum]
  refine Finset.prod_congr rfl fun l _ => ?_
  have hpow (j : ℕ) (w : ℂ) :
      gram j (complexify (g : M)) ^ w = Complex.exp ((↑(Real.log (gram j (g : M))) : ℂ) * w) := by
    rw [complexify, gram_map]
    change (↑(gram j (g : M)) : ℂ) ^ w = _
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (gram_pos g j).ne'),
      ← Complex.ofReal_log (gram_pos g j).le]
  rw [hpow, hpow, ← Complex.exp_add]
  congr 1
  ring

private theorem gramLog_shift (s a : Fin n → ℂ) (z : ℂ) (y : M) :
    gramLog (fun i => s i + z * a i) y = gramLog s y + z * gramLog a y := by
  unfold gramLog
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem extensionOfProfile_shift {ds es : List RealBlock} (a : Fin n → ℂ) (z : ℂ)
    (h : ∀ i : Fin n, realPositionExponent es i = realPositionExponent ds i + z * a i)
    (v : Cₖ) (g : G) (k : K) :
    extensionOfProfile es v (Unitary.toUnits k * g) =
      Complex.exp (z * exponentLogProfile a g k) * extensionOfProfile ds v (Unitary.toUnits k * g) := by
  let x := Unitary.toUnits k * g
  change extension (shiftedExponent n (realPositionExponent es)) v x =
    Complex.exp (z * gramLog a (x : M)) * extension (shiftedExponent n (realPositionExponent ds)) v x
  have he : shiftedExponent n (realPositionExponent es) =
      fun i => shiftedExponent n (realPositionExponent ds) i + z * a i := by
    funext i
    simp only [shiftedExponent, h i]
    ring
  simp only [extension, gramExpression_one_eq_exp]
  rw [he, gramLog_shift, Complex.exp_add]
  ring

/-- A shift in the inducing exponents changes translation on compact profiles
by an exponential scalar multiplier, smooth with values in the compact sup norm. -/
def RealStandardExponentProfileStatement : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℂ),
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, C(Matrix.unitaryGroup (Fin n) ℝ, ℂ)) ∞
      (exponentLogProfile a) ∧
    ∀ (ds es : List RealBlock) (z : ℂ),
      (∀ i : Fin n, realPositionExponent es i = realPositionExponent ds i + z * a i) →
      ∀ (v : C(Matrix.unitaryGroup (Fin n) ℝ, ℂ)) (g : Langlands.GeneralLinear n ℝ)
        (k : Matrix.unitaryGroup (Fin n) ℝ),
        extensionOfProfile es v (Unitary.toUnits k * g) =
          Complex.exp (z * exponentLogProfile a g k) * extensionOfProfile ds v (Unitary.toUnits k * g)

theorem realStandardExponentProfile : RealStandardExponentProfileStatement :=
  fun _ a => ⟨contMDiff_exponentLogProfile a, fun _ _ z h => extensionOfProfile_shift a z h⟩

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
