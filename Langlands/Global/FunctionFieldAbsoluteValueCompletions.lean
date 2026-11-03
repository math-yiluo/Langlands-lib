import Langlands.Global.FunctionFieldAbsoluteValuePlaces
import Langlands.Global.CurvePlaceCompletionCongr
import Mathlib.Topology.Algebra.UniformRing

/-! # Absolute-value and curve-place completion comparison -/

noncomputable section

universe u

open AlgebraicCurve IsDedekindDomain
open scoped NNReal

namespace Langlands.Global

section AbsoluteValue

variable {F : Type u} [Field F]

/-- The identity on the field, between its absolute-value and valuation copies. -/
def absoluteValueWithValRingEquiv (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) :
    WithAbs a ≃+* WithVal (absoluteValueValuation a ha) :=
  (WithAbs.equiv a).trans (WithVal.equiv _).symm

/-- The absolute-value and associated valuation give the same uniform structure. -/
def absoluteValueWithValUniformEquiv (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) :
    WithAbs a ≃ᵤ WithVal (absoluteValueValuation a ha) := by
  let : NormedField F := a.toNormedField
  let : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ha
  let : Valued F ℝ≥0 := NormedField.toValued
  have hv : (Valued.v : Valuation F ℝ≥0) = absoluteValueValuation a ha := by
    ext x
    rfl
  have hrefl : (absoluteValueValuation a ha).IsEquiv (absoluteValueValuation a ha) :=
    fun _ _ => Iff.rfl
  let e := WithVal.uniformEquiv hv hrefl
  have hi : Isometry (WithAbs.equiv a) :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr fun _ => rfl
  have hi' : Isometry (WithAbs.equiv a).symm :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr fun _ => rfl
  exact {
    (absoluteValueWithValRingEquiv a ha).toEquiv with
    uniformContinuous_toFun := e.symm.uniformContinuous.comp hi.uniformContinuous
    uniformContinuous_invFun := hi'.uniformContinuous.comp e.uniformContinuous
  }

/-- The completion of an absolute value equals the completion of its valuation. -/
def absoluteValueValuationCompletionEquiv (a : AbsoluteValue F ℝ)
    (ha : IsNonarchimedean a) :
    a.Completion ≃+* (absoluteValueValuation a ha).Completion :=
  UniformSpace.Completion.mapRingEquiv (absoluteValueWithValRingEquiv a ha)
    (absoluteValueWithValUniformEquiv a ha).continuous
    (absoluteValueWithValUniformEquiv a ha).symm.continuous

theorem continuous_absoluteValueValuationCompletionEquiv
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) :
    Continuous (absoluteValueValuationCompletionEquiv a ha) :=
  UniformSpace.Completion.continuous_map

theorem continuous_absoluteValueValuationCompletionEquiv_symm
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) :
    Continuous (absoluteValueValuationCompletionEquiv a ha).symm :=
  UniformSpace.Completion.continuous_map

/-- The same completion equivalence as a homeomorphism. -/
def absoluteValueValuationCompletionHomeomorph
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) :
    a.Completion ≃ₜ (absoluteValueValuation a ha).Completion where
  toEquiv := (absoluteValueValuationCompletionEquiv a ha).toEquiv
  continuous_toFun := continuous_absoluteValueValuationCompletionEquiv a ha
  continuous_invFun := continuous_absoluteValueValuationCompletionEquiv_symm a ha

theorem absoluteValueValuationCompletionEquiv_coe
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) (x : F) :
    absoluteValueValuationCompletionEquiv a ha
      ((WithAbs.toAbs a x : WithAbs a) : a.Completion) =
        ((WithVal.toVal (absoluteValueValuation a ha) x :
          WithVal (absoluteValueValuation a ha)) :
            (absoluteValueValuation a ha).Completion) := by
  change UniformSpace.Completion.map (absoluteValueWithValRingEquiv a ha)
    ((WithAbs.toAbs a x : WithAbs a) : a.Completion) = _
  have hu : UniformContinuous (absoluteValueWithValRingEquiv a ha) :=
    (absoluteValueWithValUniformEquiv a ha).uniformContinuous
  rw [UniformSpace.Completion.map_coe hu]
  rfl

/-- The strong triangle inequality extends to the actual absolute-value completion. -/
theorem absoluteValueCompletion_norm_add_le_max
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) (x y : a.Completion) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro x y
  rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact ha x.ofAbs y.ofAbs

/-- The closed absolute-value unit ball equals the completed valuation ring. -/
theorem absoluteValueValuationCompletionEquiv_le_one_iff
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) (x : a.Completion) :
    ‖x‖ ≤ 1 ↔ Valued.v (absoluteValueValuationCompletionEquiv a ha x) ≤ 1 := by
  let : IsUltrametricDist a.Completion :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (absoluteValueCompletion_norm_add_le_max a ha)
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · have hn : IsClopen {x : a.Completion | ‖x‖ ≤ 1} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        (IsUltrametricDist.isClopen_closedBall (0 : a.Completion)
          (one_ne_zero : (1 : ℝ) ≠ 0))
    exact (absoluteValueValuationCompletionHomeomorph a ha).isClosed_setOfPred_iff hn
      (Valued.isClopen_valuationSubring _)
  · intro x
    rw [show (x : a.Completion) =
      ((WithAbs.toAbs a x.ofAbs : WithAbs a) : a.Completion) from rfl,
      absoluteValueValuationCompletionEquiv_coe, Valued.valuedCompletion_apply,
      UniformSpace.Completion.norm_coe]
    rfl

/-- The completed valuation ring associated to a nonarchimedean absolute value. -/
def absoluteValueCompletionIntegers
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) : ValuationSubring a.Completion :=
  (Valued.v : Valuation (absoluteValueValuation a ha).Completion ℝ≥0).valuationSubring.comap
    (absoluteValueValuationCompletionEquiv a ha).toRingHom

@[simp]
theorem mem_absoluteValueCompletionIntegers
    (a : AbsoluteValue F ℝ) (ha : IsNonarchimedean a) (x : a.Completion) :
    x ∈ absoluteValueCompletionIntegers a ha ↔ ‖x‖ ≤ 1 :=
  (absoluteValueValuationCompletionEquiv_le_one_iff a ha x).symm

end AbsoluteValue

section EquivalentValuations

variable {F Γ Δ : Type*} [Field F]
variable [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
variable {v : Valuation F Γ} {w : Valuation F Δ}

/-- Equivalent valuations of the same field give the identity comparison of completions. -/
def equivalentValuationCompletionRingEquiv (h : v.IsEquiv w) :
    v.Completion ≃+* w.Completion :=
  UniformSpace.Completion.mapRingEquiv (WithVal.congr v w (.refl F))
    h.uniformEquiv.continuous h.uniformEquiv.symm.continuous

theorem continuous_equivalentValuationCompletionRingEquiv (h : v.IsEquiv w) :
    Continuous (equivalentValuationCompletionRingEquiv h) :=
  UniformSpace.Completion.continuous_map

theorem continuous_equivalentValuationCompletionRingEquiv_symm (h : v.IsEquiv w) :
    Continuous (equivalentValuationCompletionRingEquiv h).symm :=
  UniformSpace.Completion.continuous_map

theorem equivalentValuationCompletionRingEquiv_coe (h : v.IsEquiv w) (x : F) :
    equivalentValuationCompletionRingEquiv h
      ((WithVal.toVal v x : WithVal v) : v.Completion) =
        ((WithVal.toVal w x : WithVal w) : w.Completion) := by
  change UniformSpace.Completion.map (WithVal.congr v w (.refl F))
    ((WithVal.toVal v x : WithVal v) : v.Completion) = _
  rw [UniformSpace.Completion.map_coe h.uniformContinuous_congr]
  rfl

theorem equivalentValuationCompletionRingEquiv_le_one_iff
    (h : v.IsEquiv w) (x : v.Completion) :
    Valued.v x ≤ 1 ↔ Valued.v (equivalentValuationCompletionRingEquiv h x) ≤ 1 :=
  h.valuedCompletion_le_one_iff

end EquivalentValuations

section FunctionField

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Compare the actual completion of an arbitrary nontrivial absolute value with
its curve place's existing adic completion. -/
def functionFieldAbsoluteValueCompletionEquiv
    (a : NontrivialRealAbsoluteValue (F := F)) :
    a.val.Completion ≃+*
      (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletion F :=
  (absoluteValueValuationCompletionEquiv a.val
    (finiteConstants_absoluteValue_isNonarchimedean k F a.val)).trans
    ((equivalentValuationCompletionRingEquiv
      (functionFieldAbsoluteValueValuation_isEquiv_adicValuation k F a)).trans
      (HeightOneSpectrum.adicCompletion.equiv F
        (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum).symm)

theorem continuous_functionFieldAbsoluteValueCompletionEquiv
    (a : NontrivialRealAbsoluteValue (F := F)) :
    Continuous (functionFieldAbsoluteValueCompletionEquiv k F a) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _).comp
    ((continuous_equivalentValuationCompletionRingEquiv
      (functionFieldAbsoluteValueValuation_isEquiv_adicValuation k F a)).comp
      (continuous_absoluteValueValuationCompletionEquiv _ _))

theorem continuous_functionFieldAbsoluteValueCompletionEquiv_symm
    (a : NontrivialRealAbsoluteValue (F := F)) :
    Continuous (functionFieldAbsoluteValueCompletionEquiv k F a).symm :=
  (continuous_absoluteValueValuationCompletionEquiv_symm _ _).comp
    ((continuous_equivalentValuationCompletionRingEquiv_symm
      (functionFieldAbsoluteValueValuation_isEquiv_adicValuation k F a)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion _ _))

/-- The completed-field comparison preserves the actual existing topologies. -/
def functionFieldAbsoluteValueCompletionHomeomorph
    (a : NontrivialRealAbsoluteValue (F := F)) :
    a.val.Completion ≃ₜ
      (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletion F where
  toEquiv := (functionFieldAbsoluteValueCompletionEquiv k F a).toEquiv
  continuous_toFun := continuous_functionFieldAbsoluteValueCompletionEquiv k F a
  continuous_invFun := continuous_functionFieldAbsoluteValueCompletionEquiv_symm k F a

theorem functionFieldAbsoluteValueCompletionEquiv_coe
    (a : NontrivialRealAbsoluteValue (F := F)) (x : F) :
    functionFieldAbsoluteValueCompletionEquiv k F a
      ((WithAbs.toAbs a.val x : WithAbs a.val) : a.val.Completion) =
        algebraMap F
          ((functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletion F) x := by
  apply HeightOneSpectrum.adicCompletion.ext
  change equivalentValuationCompletionRingEquiv
    (functionFieldAbsoluteValueValuation_isEquiv_adicValuation k F a)
    (absoluteValueValuationCompletionEquiv a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val)
      ((WithAbs.toAbs a.val x : WithAbs a.val) : a.val.Completion)) = _
  rw [absoluteValueValuationCompletionEquiv_coe,
    equivalentValuationCompletionRingEquiv_coe]
  rfl

theorem functionFieldAbsoluteValueCompletionEquiv_mem_integers_iff
    (a : NontrivialRealAbsoluteValue (F := F)) (x : a.val.Completion) :
    functionFieldAbsoluteValueCompletionEquiv k F a x ∈
      (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletionIntegers F ↔
        ‖x‖ ≤ 1 := by
  change Valued.v (equivalentValuationCompletionRingEquiv
    (functionFieldAbsoluteValueValuation_isEquiv_adicValuation k F a)
      (absoluteValueValuationCompletionEquiv a.val
        (finiteConstants_absoluteValue_isNonarchimedean k F a.val) x)) ≤ 1 ↔ _
  rw [← equivalentValuationCompletionRingEquiv_le_one_iff,
    ← absoluteValueValuationCompletionEquiv_le_one_iff]

/-- The completed-field comparison restricts to the closed unit balls. -/
def functionFieldAbsoluteValueCompletionIntegersEquiv
    (a : NontrivialRealAbsoluteValue (F := F)) :
    absoluteValueCompletionIntegers a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val) ≃+*
        (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletionIntegers F :=
  (functionFieldAbsoluteValueCompletionEquiv k F a).restrict
    (absoluteValueCompletionIntegers a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val))
    ((functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletionIntegers F)
    fun x =>
      (mem_absoluteValueCompletionIntegers a.val
        (finiteConstants_absoluteValue_isNonarchimedean k F a.val) x).trans
        (functionFieldAbsoluteValueCompletionEquiv_mem_integers_iff k F a x).symm

@[simp]
theorem coe_functionFieldAbsoluteValueCompletionIntegersEquiv
    (a : NontrivialRealAbsoluteValue (F := F))
    (x : absoluteValueCompletionIntegers a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val)) :
    (functionFieldAbsoluteValueCompletionIntegersEquiv k F a x :
      (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletion F) =
        functionFieldAbsoluteValueCompletionEquiv k F a x := rfl

/-- The integral-ring comparison respects the existing subspace topologies. -/
def functionFieldAbsoluteValueCompletionIntegersHomeomorph
    (a : NontrivialRealAbsoluteValue (F := F)) :
    absoluteValueCompletionIntegers a.val
      (finiteConstants_absoluteValue_isNonarchimedean k F a.val) ≃ₜ
        (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletionIntegers F where
  toEquiv := (functionFieldAbsoluteValueCompletionIntegersEquiv k F a).toEquiv
  continuous_toFun :=
    ((continuous_functionFieldAbsoluteValueCompletionEquiv k F a).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_functionFieldAbsoluteValueCompletionEquiv_symm k F a).comp
      continuous_subtype_val).subtype_mk _

end FunctionField

end Langlands.Global
