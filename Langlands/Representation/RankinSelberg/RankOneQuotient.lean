import Langlands.Representation.RankinSelberg.Measures
import Langlands.Analysis.Local.QuotientMeasure

/-!
# The actual rank-one unipotent quotient measure

The subgroup `N₁` is trivial. Its normalized Haar measure is unit point mass,
and the quotient is canonically homeomorphic to `GL₁`. We construct the
quotient measure and prove the complete Weil compatibility property.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure QuotientIntegration

universe uF

variable {F : Type uF} [Field F]

/-- In rank one, the actual upper-unipotent subgroup consists of the identity. -/
theorem upperUnipotent_one_eq_bot :
    GeneralLinear.upperUnipotent 1 F = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simpa using hg.2 i

instance upperUnipotent_one_subsingleton :
    Subsingleton (GeneralLinear.upperUnipotent 1 F) := by
  rw [upperUnipotent_one_eq_bot]
  infer_instance

/-- Commutativity here is proved from the actual one-by-one matrix product. -/
theorem rankOne_mul_comm (g h : Matrix.GeneralLinearGroup (Fin 1) F) :
    g * h = h * g := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  change (g.val * h.val) 0 0 = (h.val * g.val) 0 0
  simp [Matrix.mul_apply, mul_comm]

section Topology

variable [TopologicalSpace F]

/-- The actual quotient `N₁ \ GL₁` has no nontrivial identifications. -/
def rankOneQuotientHomeomorph :
    LeftQuotient (GeneralLinear.upperUnipotent 1 F) ≃ₜ
      Matrix.GeneralLinearGroup (Fin 1) F :=
  (Homeomorph.Quotient.congrRight (by
    intro x y
    rw [QuotientGroup.rightRel_apply, upperUnipotent_one_eq_bot]
    change (y * x⁻¹ ∈ (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 1) F))) ↔ x = y
    simp only [Subgroup.mem_bot, mul_inv_eq_one]
    exact eq_comm)).trans Homeomorph.quotientBot

@[simp] theorem rankOneQuotientHomeomorph_mk (g : Matrix.GeneralLinearGroup (Fin 1) F) :
    rankOneQuotientHomeomorph (Quotient.mk _ g) = g := rfl

@[simp] theorem rankOneQuotientHomeomorph_symm_apply
    (g : Matrix.GeneralLinearGroup (Fin 1) F) :
    rankOneQuotientHomeomorph.symm g = Quotient.mk _ g := rfl

end Topology

section LocalField

variable (F) [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 1) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin 1) F)]
variable [MeasurableSpace (GeneralLinear.upperUnipotent 1 F)]
  [BorelSpace (GeneralLinear.upperUnipotent 1 F)]

/-- The normalized rank-one ambient Haar measure is also right invariant. -/
instance generalLinearHaar_rankOne_rightInvariant :
    IsMulRightInvariant (generalLinearHaar F 0) where
  map_mul_right_eq_self g := by
    have hc : (fun x : Matrix.GeneralLinearGroup (Fin 1) F => x * g) =
        (fun x => g * x) := funext (fun x => rankOne_mul_comm x g)
    rw [hc]
    exact map_mul_left_eq_self (generalLinearHaar F 0) g

/-- Every translation of the trivial rank-one unipotent group is the identity. -/
instance unipotentHaar_rankOne_rightInvariant :
    IsMulRightInvariant (unipotentHaar F 0) where
  map_mul_right_eq_self h := by
    have : Subsingleton (GeneralLinear.upperUnipotent (0 + 1) F) :=
      upperUnipotent_one_subsingleton
    have hh : h = 1 := Subsingleton.elim _ _
    subst h
    simpa only [mul_one] using (Measure.map_id' (μ := unipotentHaar F 0))

omit [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 1) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin 1) F)] in
/-- The existing integral normalization makes unipotent Haar exactly unit point mass. -/
theorem unipotentHaar_rankOne_eq_dirac :
    unipotentHaar F 0 = Measure.dirac 1 := by
  have : Subsingleton (GeneralLinear.upperUnipotent (0 + 1) F) :=
    upperUnipotent_one_subsingleton
  have hK : (unipotentIntegralOpen F 0 :
      Set (GeneralLinear.upperUnipotent 1 F)) = Set.univ := by
    ext h
    simp only [Set.mem_univ, iff_true]
    have hh : h = 1 := Subsingleton.elim _ _
    subst h
    exact (unipotentIntegralOpen F 0).one_mem
  have hmass : unipotentHaar F 0 Set.univ = 1 := by
    simpa only [hK] using unipotentHaar_integral F 0
  ext s hs
  by_cases h : (1 : GeneralLinear.upperUnipotent 1 F) ∈ s
  · have he : s = Set.univ := Set.eq_univ_iff_forall.mpr (fun x => by
      have hx : x = 1 := Subsingleton.elim _ _
      subst x
      exact h)
    simp [he, hmass]
  · have he : s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx1 : x = 1 := Subsingleton.elim _ _
      subst x
      exact h hx
    simp [he]

omit [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 1) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin 1) F)] in
@[simp] theorem quotientAverage_rankOne_mk
    (f : Matrix.GeneralLinearGroup (Fin 1) F → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 1) F) :
    quotientAverage (GeneralLinear.upperUnipotent 1 F) (unipotentHaar F 0) f
      (Quotient.mk _ g) = f g := by
  rw [quotientAverage_mk, unipotentHaar_rankOne_eq_dirac]
  have hf : (fun h : GeneralLinear.upperUnipotent 1 F => f (h.val * g)) =
      fun _ => f g := by
    funext h
    have hh : h = 1 := Subsingleton.elim _ _
    simp only [hh, OneMemClass.coe_one, one_mul]
  rw [hf]
  simp

variable [MeasurableSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 F))]
  [BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 F))]

/-- The actual rank-one quotient measure, with the existing integral-group normalization. -/
def rankOneQuotientHaar :
    Measure (LeftQuotient (GeneralLinear.upperUnipotent 1 F)) :=
  Measure.map rankOneQuotientHomeomorph.symm (generalLinearHaar F 0)

instance rankOneQuotientHaar_regular : (rankOneQuotientHaar F).Regular :=
  Measure.Regular.map rankOneQuotientHomeomorph.symm

omit [MeasurableSpace (GeneralLinear.upperUnipotent 1 F)]
  [BorelSpace (GeneralLinear.upperUnipotent 1 F)] in
/-- The image of the actual integral matrix subgroup has quotient mass one. -/
@[simp] theorem rankOneQuotientHaar_integralSubgroup :
    rankOneQuotientHaar F
      (rankOneQuotientHomeomorph.symm ''
        (Conductor.integralSubgroup (ValuativeRel.valuation F).integer 0 :
          Set (Matrix.GeneralLinearGroup (Fin 1) F))) = 1 := by
  rw [rankOneQuotientHaar]
  change (Measure.map rankOneQuotientHomeomorph.symm.toMeasurableEquiv
    (generalLinearHaar F 0)) _ = 1
  rw [rankOneQuotientHomeomorph.symm.toMeasurableEquiv.measurableEmbedding.map_apply]
  change generalLinearHaar F 0
    (rankOneQuotientHomeomorph.symm ⁻¹'
      (rankOneQuotientHomeomorph.symm ''
        (Conductor.integralSubgroup (ValuativeRel.valuation F).integer 0 :
          Set (Matrix.GeneralLinearGroup (Fin 1) F)))) = 1
  rw [Set.preimage_image_eq _ rankOneQuotientHomeomorph.symm.injective]
  exact generalLinearHaar_integralSubgroup F 0

omit [MeasurableSpace (GeneralLinear.upperUnipotent 1 F)]
  [BorelSpace (GeneralLinear.upperUnipotent 1 F)] in
theorem integral_rankOneQuotientHaar
    (f : LeftQuotient (GeneralLinear.upperUnipotent 1 F) → ℂ) :
    (∫ q, f q ∂rankOneQuotientHaar F) =
      ∫ g, f (Quotient.mk _ g) ∂generalLinearHaar F 0 :=
  integral_map_equiv rankOneQuotientHomeomorph.symm.toMeasurableEquiv f

omit [MeasurableSpace (GeneralLinear.upperUnipotent 1 F)]
  [BorelSpace (GeneralLinear.upperUnipotent 1 F)] in
theorem rankOneQuotientHaar_right_invariant
    (g : Matrix.GeneralLinearGroup (Fin 1) F) :
    MeasurePreserving (rightTranslate (GeneralLinear.upperUnipotent 1 F) g)
      (rankOneQuotientHaar F) (rankOneQuotientHaar F) := by
  refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
  rw [rankOneQuotientHaar, Measure.map_map (rightTranslate _ g).continuous.measurable
    rankOneQuotientHomeomorph.symm.continuous.measurable]
  change Measure.map (fun x : Matrix.GeneralLinearGroup (Fin 1) F =>
    Quotient.mk _ (x * g)) (generalLinearHaar F 0) =
      Measure.map rankOneQuotientHomeomorph.symm (generalLinearHaar F 0)
  change Measure.map (rankOneQuotientHomeomorph.symm ∘ fun x => x * g)
    (generalLinearHaar F 0) = _
  rw [← Measure.map_map rankOneQuotientHomeomorph.symm.continuous.measurable
    (measurable_mul_const g), map_mul_right_eq_self]

/-- The rank-one quotient measure satisfies the full compatibility property for
the actual, already normalized group and unipotent Haar measures. -/
theorem rankOneQuotientHaar_isCompatible :
    IsCompatible (GeneralLinear.upperUnipotent 1 F)
      (generalLinearHaar F 0) (unipotentHaar F 0) (rankOneQuotientHaar F) where
  nonzero := by
    apply (Measure.map_ne_zero_iff
      rankOneQuotientHomeomorph.symm.continuous.measurable.aemeasurable).2
    intro hzero
    have hm := generalLinearHaar_integralSubgroup F 0
    rw [hzero] at hm
    simp at hm
  regular := inferInstance
  right_invariant := rankOneQuotientHaar_right_invariant F
  averaging_integrable f hf hc := by
    apply (integrable_map_equiv rankOneQuotientHomeomorph.symm.toMeasurableEquiv _).2
    change Integrable (fun x : Matrix.GeneralLinearGroup (Fin 1) F =>
      quotientAverage (GeneralLinear.upperUnipotent 1 F) (unipotentHaar F 0) f
        (Quotient.mk _ x)) (generalLinearHaar F 0)
    simpa only [quotientAverage_rankOne_mk] using
      hf.integrable_of_hasCompactSupport hc (μ := generalLinearHaar F 0)
  integral_formula f _ _ := by
    rw [integral_rankOneQuotientHaar]
    simp only [quotientAverage_rankOne_mk]

/-- Genuine existence for rank one, with no assumed quotient measure. -/
theorem rankOne_compatibleMeasureExists :
    CompatibleMeasureExists (GeneralLinear.upperUnipotent 1 F)
      (generalLinearHaar F 0) (unipotentHaar F 0) :=
  ⟨rankOneQuotientHaar F, rankOneQuotientHaar_isCompatible F⟩

end LocalField

end Langlands.RankinSelberg
