import Langlands.Global.RankinSelberg.ComplexJacquetJointContinuity
import Langlands.Global.RankinSelberg.ComplexJacquetShiftedLie

/-! # The integrated right Lie identity of canonical complex Jacquet coefficients -/

noncomputable section

open Filter MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Analysis.SeveralComplex (differentiableOn_intervalIntegral_of_continuousOn)
open Langlands.Archimedean (complexStandardLie matrixModel rightDerivative rightDerivative_eq_fderiv
  contDiffAt_unitsExtension unitsExtension unitsExtension_val principalSeriesLie_one_tmul_apply_coe
  rightDerivative_smul_left)
open Langlands.Archimedean.ComplexExponentDeformation (transportedDerivative)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile
  standardSection_unitary standardSection)
open ComplexGodementGeneratorFamily (isStrictlyDominant_characterList)
open ComplexJacquetChamberHolomorphic (chamber isOpen_chamber)
open ComplexJacquetChamberIntertwiner (chamberIntertwiner isComplexWhittakerIntertwiner_chamberIntertwiner)

attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "P" => (I → ℂ)
local notation "M" => Matrix I I ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)

private theorem shiftJacquetExponent_apply (p : P) (i j : I) (z : ℂ) :
    shiftJacquetExponent p i z j = if j = i then p j + z else p j := by
  by_cases h : j = i
  · simp [shiftJacquetExponent, h]
  · simp [shiftJacquetExponent, h]

private theorem eq_of_coordinate_differentiable_eqOn_chamber {F H : P → ℂ}
    (hF : ∀ p i, Differentiable ℂ (F ∘ shiftJacquetExponent p i))
    (hH : ∀ p i, Differentiable ℂ (H ∘ shiftJacquetExponent p i))
    (hEq : EqOn F H (chamber r)) : F = H := by
  let p : P := fun i => -((i : ℕ) : ℂ)
  have hp : p ∈ chamber r := by
    intro i
    change (-((i.succ : ℕ) : ℂ)).re < (-((i.castSucc : ℕ) : ℂ)).re
    simp only [Complex.neg_re, Complex.natCast_re, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
      Nat.cast_one, Complex.add_re, Complex.one_re]
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chamber (r := r)) p hp
  have hS (S : Finset I) : ∀ q : P, (∀ j ∉ S, dist (q j) (p j) < δ) → F q = H q := by
    induction S using Finset.induction_on with
    | empty =>
      intro q hq
      exact hEq (hball ((dist_pi_lt_iff hδ).mpr (fun j => hq j (by simp))))
    | insert i S hi ih =>
      intro q hq
      let c := Function.update q i (p i)
      let L := shiftJacquetExponent c i
      have hL : ∀ᶠ z : ℂ in 𝓝 0, (F ∘ L) z = (H ∘ L) z := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with z hz
        apply ih (L z)
        intro j hj
        change dist (shiftJacquetExponent c i z j) (p j) < δ
        rw [shiftJacquetExponent_apply]
        by_cases hji : j = i
        · subst j
          simp only [ite_true, c, Function.update_self]
          rw [dist_eq_norm, show p i + z - p i = z by abel]
          simpa only [Metric.mem_ball, dist_zero_right] using hz
        · simpa only [ite_eq_right hji, c, Function.update_of_ne hji] using
            hq j (by simp [hji, hj])
      have hh := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => (hF c i).analyticAt z)
        (fun z _ => (hH c i).analyticAt z) hL
      have hqL : L (q i - p i) = q := by
        funext j
        change shiftJacquetExponent c i (q i - p i) j = q j
        rw [shiftJacquetExponent_apply]
        by_cases hji : j = i
        · subst j
          simp only [ite_true, c, Function.update_self]
          abel
        · simp [hji, c, Function.update_of_ne]
      have he : F (L (q i - p i)) = H (L (q i - p i)) := congrFun hh (q i - p i)
      rwa [hqL] at he
  funext q
  exact hS Finset.univ q (by simp)

private theorem transferProfile_trans (l : I → ℤ) (p q t : P) (f : Std[l, p]) :
    transferProfile l q t (transferProfile l p q f) = transferProfile l p t f := by
  have h : compactRestriction (transferProfile l p q f).val = compactRestriction f.val :=
    funext (standardSection_unitary q (compactRestriction f.val))
  exact Subtype.ext (congrArg (standardSection t) h)

private def LieDirection (l : I → ℤ) (p : P) (f : Std[l, p]) : M →ₗ[ℝ] Std[l, p] where
  toFun X := complexStandardLie n (characterList l p) (1 ⊗ₜ X) f
  map_add' X Y := by rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
  map_smul' c X := by
    apply Subtype.ext
    change (complexStandardLie n (characterList l p) (1 ⊗ₜ (c • X)) f).val =
      c • (complexStandardLie n (characterList l p) (1 ⊗ₜ X) f).val
    simp only [principalSeriesLie_one_tmul_apply_coe, rightDerivative_smul_left]

private theorem lieDirection_apply (l : I → ℤ) (p : P) (f : Std[l, p]) (X : M) :
    LieDirection l p f X = complexStandardLie n (characterList l p) (1 ⊗ₜ X) f := rfl

private theorem continuedJacquet_chamber_lie (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : I → ℤ) (p : P) (hp : p ∈ chamber r) (f : Std[l, p]) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (continuedJacquet μ a l p f) ∧
      ∀ X : M, continuedJacquet μ a l p (LieDirection l p f X) =
        rightDerivative (matrixModel ℂ n) X (continuedJacquet μ a l p f) := by
  let ds := characterList l p
  let e := isStrictlyDominant_characterList l hp
  let B := chamberIntertwiner μ ds a e
  have hB := isComplexWhittakerIntertwiner_chamberIntertwiner μ ds List.length_ofFn a e
  have he (v : Std[l, p]) : continuedJacquet μ a l p v = B v := continuedJacquet_chamber μ a l p hp v
  rw [he]
  refine ⟨hB.2.1 f, fun X => ?_⟩
  rw [he]
  exact hB.2.2.2.2 X f (LieDirection l p f X)
    (principalSeriesLie_one_tmul_apply_coe ℂ n _ X f)

private theorem continuous_shifted_basis_evaluation (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : I → ℤ) (p : P) (i : I) (X : M) (f : Std[l, p]) (γ : ℝ → G) (hγ : Continuous γ) :
    Continuous (fun w : ℂ × ℝ =>
      let q := shiftJacquetExponent p i w.1
      continuedJacquet μ a l q (LieDirection l q (transferProfile l p q f) X) (γ w.2)) := by
  let ds := characterList l p
  let L₀ := complexStandardLie n ds (1 ⊗ₜ X)
  let L₁ := transportedDerivative ds (List.length_ofFn : ds.length = n) i 1 X - L₀
  let B := continuedJacquetFamilies μ a l p
  let q := shiftJacquetExponent p i
  have hc (v : Std[l, p]) : Continuous (fun w : ℂ × ℝ => B v (q w.1) (γ w.2)) :=
    (complexJacquetJointContinuity μ a l _ (compactRestriction_isCompactProfile v.2)).comp
      ((((differentiable_shiftJacquetExponent p i).continuous).comp continuous_fst).prodMk
        (hγ.comp continuous_snd))
  have he (w : ℂ × ℝ) :
      continuedJacquet μ a l (q w.1) (LieDirection l (q w.1) (transferProfile l p (q w.1) f) X) (γ w.2) =
        B (L₀ f) (q w.1) (γ w.2) + w.1 * B (L₁ f) (q w.1) (γ w.2) :=
    continuedJacquet_shiftedLie_apply μ a l p i X f w.1 (γ w.2)
  change Continuous (fun w : ℂ × ℝ =>
    continuedJacquet μ a l (q w.1) (LieDirection l (q w.1) (transferProfile l p (q w.1) f) X) (γ w.2))
  simp_rw [he]
  exact (hc (L₀ f)).add (continuous_fst.mul (hc (L₁ f)))

/-- The fundamental theorem of calculus for canonical Jacquet evaluation along a curve
whose ambient matrix derivative is given by a continuous right Lie direction. -/
def ComplexJacquetIntegratedLieStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P) (f : Std[l, p])
    (γ : ℝ → G) (V : ℝ → M), Continuous γ → Continuous V →
    ∀ (b c : ℝ), b ≤ c →
      (∀ t ∈ Ioo b c, HasDerivAt (fun v => (γ v).val) ((γ t).val * V t) t) →
      (∫ t in b..c, continuedJacquet μ a l p
        (complexStandardLie n (characterList l p) (1 ⊗ₜ (V t)) f) (γ t)) =
        continuedJacquet μ a l p f (γ c) - continuedJacquet μ a l p f (γ b)

set_option maxHeartbeats 900000 in
theorem complexJacquetIntegratedLie : ComplexJacquetIntegratedLieStatement (r := r) := by
  intro μ a l p f γ V hγ hV b c hbc hcurve
  let S (q : P) := transferProfile l p q f
  let J (q : P) := continuedJacquet μ a l q
  let D (q : P) (X : M) (t : ℝ) := J q (LieDirection l q (S q) X) (γ t)
  let K (q : P) (t : ℝ) := D q (V t) t
  let F (q : P) := ∫ t in b..c, K q t
  let H (q : P) := J q (S q) (γ c) - J q (S q) (γ b)
  let e := Module.finBasis ℝ M
  have hsum (q : P) (t : ℝ) : K q t = ∑ j, ((e.repr (V t) j : ℝ) : ℂ) * D q (e j) t := by
    change J q (LieDirection l q (S q) (V t)) (γ t) = _
    conv_lhs => rw [← e.sum_repr (V t)]
    simp only [map_sum, map_smul, LinearMap.map_smul_of_tower, Finset.sum_apply, Pi.smul_apply, Complex.real_smul, D]
  have hDline (q : P) (i : I) (X : M) (t : ℝ) :
      Differentiable ℂ (fun z => D (shiftJacquetExponent q i z) X t) := by
    have h := complexJacquetShiftedLie μ a l q i X (S q) (γ t)
    have he (z : ℂ) : transferProfile l q (shiftJacquetExponent q i z) (S q) =
        S (shiftJacquetExponent q i z) := transferProfile_trans l p q _ f
    change Differentiable ℂ (fun z => continuedJacquet μ a l (shiftJacquetExponent q i z)
      (complexStandardLie n (characterList l (shiftJacquetExponent q i z)) (1 ⊗ₜ X)
        (transferProfile l q (shiftJacquetExponent q i z) (S q))) (γ t)) at h
    simpa only [he, D, lieDirection_apply, J] using h
  have hDcont (q : P) (i : I) (X : M) :
      Continuous (fun w : ℂ × ℝ => D (shiftJacquetExponent q i w.1) X w.2) := by
    have he (z : ℂ) : transferProfile l q (shiftJacquetExponent q i z) (S q) =
        S (shiftJacquetExponent q i z) := transferProfile_trans l p q _ f
    have h := continuous_shifted_basis_evaluation μ a l q i X (S q) γ hγ
    simpa only [he, D, J] using h
  have hKcont (q : P) (i : I) :
      Continuous (fun w : ℂ × ℝ => K (shiftJacquetExponent q i w.1) w.2) := by
    simp_rw [hsum]
    apply continuous_finsetSum
    intro j _
    have hc : Continuous (fun t => e.repr (V t) j) :=
      (e.coord j).toContinuousLinearMap.continuous.comp hV
    exact (Complex.continuous_ofReal.comp (hc.comp continuous_snd)).mul (hDcont q i (e j))
  have hF (q : P) (i : I) : Differentiable ℂ (F ∘ shiftJacquetExponent q i) := by
    have hd (t : ℝ) : Differentiable ℂ (fun z => K (shiftJacquetExponent q i z) t) := by
      simp_rw [hsum]
      exact Differentiable.fun_sum fun j _ => (hDline q i (e j) t).const_mul _
    exact differentiableOn_univ.mp (differentiableOn_intervalIntegral_of_continuousOn
      isOpen_univ (hKcont q i).continuousOn (fun t => (hd t).differentiableOn) b c)
  have hH : Differentiable ℂ H := by
    have hd (g : G) : Differentiable ℂ (fun q => J q (S q) g) := by
      simp only [J, S, continuedJacquet_transferProfile]
      exact (canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile f.2)).2.1 g
    exact (hd (γ c)).sub (hd (γ b))
  have hEq : EqOn F H (chamber r) := by
    intro q hq
    have hW := continuedJacquet_chamber_lie μ a l q hq (S q)
    have hcont : Continuous (K q) := by
      have h := (hKcont q 0).comp ((continuous_const (y := (0 : ℂ))).prodMk continuous_id)
      simpa only [Function.comp_def, shiftJacquetExponent, zero_smul, add_zero, id_eq] using h
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbc
      ((hW.1.continuous.comp hγ).continuousOn) (fun t ht => ?_) (hcont.intervalIntegrable b c)
    let g := γ t
    let W := J q (S q)
    have hW' : ContDiffAt ℝ ∞ (unitsExtension W) g.val := contDiffAt_unitsExtension hW.1 g
    have hd := (hW'.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hcurve t ht)
    have he : unitsExtension W ∘ (fun v => (γ v).val) = fun v => W (γ v) :=
      funext fun v => unitsExtension_val W (γ v)
    rw [he] at hd
    have hL : K q t = fderiv ℝ (unitsExtension W) g.val (g.val * V t) := by
      change J q (LieDirection l q (S q) (V t)) g = _
      rw [hW.2, rightDerivative_eq_fderiv hW.1]
    change HasDerivAt (fun v => W (γ v)) (K q t) t
    rw [hL]
    exact hd
  have h := congrFun (eq_of_coordinate_differentiable_eqOn_chamber hF
    (fun q i => hH.comp (differentiable_shiftJacquetExponent q i)) hEq) p
  simpa only [H, F, K, D, J, S, lieDirection_apply, transferProfile_self] using h

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
