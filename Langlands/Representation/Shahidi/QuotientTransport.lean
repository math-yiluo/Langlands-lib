import Langlands.Group.GL.UpperBruhatEmbedding
import Langlands.Group.GL.UpperUnipotent
import Langlands.Analysis.Local.QuotientMeasure

/-! # The inverse-transpose quotient transport in Shahidi's measure item 1 -/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear QuotientIntegration MeasureTheory

universe uF

variable (n : ℕ) (F : Type uF) [CommRing F]

/-- The actual automorphism `a ↦ wₙ (a⁻¹)ᵀ wₙ⁻¹`. -/
def quotientReflection : Langlands.GeneralLinear n F ≃* Langlands.GeneralLinear n F :=
  (inverseTranspose n F).trans (MulAut.conj (weylLong n F))

@[simp] theorem quotientReflection_apply (g : Langlands.GeneralLinear n F) :
    quotientReflection n F g = weylLong n F * inverseTranspose n F g * weylLong n F := by
  simp only [quotientReflection, MulEquiv.trans_apply, MulAut.conj_apply, weylLong_inv]

@[simp] theorem quotientReflection_involutive (g : Langlands.GeneralLinear n F) :
    quotientReflection n F (quotientReflection n F g) = g := by
  rw [quotientReflection_apply, quotientReflection_apply]
  simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive]
  simp only [← mul_assoc, weylLong_mul_self, one_mul]
  simp only [mul_assoc, weylLong_mul_self, mul_one]

/-- In lower-right block coordinates, this is exactly the larger-group map
`a ↦ w_(n+1) (diag(a,1)⁻¹)ᵀ w_(n+1)⁻¹` from measure item 1. -/
theorem quotientReflection_insert (g : Langlands.GeneralLinear n F) :
    Bruhat.insert 0 (quotientReflection n F g) =
      weylLong (n + 1) F * inverseTranspose (n + 1) F
        (Bruhat.insert (Fin.last n) g) * weylLong (n + 1) F := by
  apply Units.ext
  ext i j
  rw [weylLong_conjugate_entry, inverseTranspose_entry, ← map_inv]
  induction i using Fin.succAboveCases (0 : Fin (n + 1)) with
  | x =>
    induction j using Fin.succAboveCases (0 : Fin (n + 1)) with
    | x => simp only [Fin.rev_zero, Bruhat.insert_p_p]
    | p j => simp only [Fin.rev_succAbove, Fin.rev_zero, Bruhat.insert_p_succAbove,
        Bruhat.insert_succAbove_p]
  | p i =>
    induction j using Fin.succAboveCases (0 : Fin (n + 1)) with
    | x => simp only [Fin.rev_succAbove, Fin.rev_zero, Bruhat.insert_p_succAbove,
        Bruhat.insert_succAbove_p]
    | p j => simp only [Fin.rev_succAbove, Fin.rev_zero,
        Bruhat.insert_succAbove_succAbove, quotientReflection_apply,
        weylLong_conjugate_entry, inverseTranspose_entry]

/-- The automorphism preserves the actual upper-unipotent subgroup in every rank. -/
theorem quotientReflection_mem (u : Langlands.GeneralLinear n F)
    (hu : u ∈ upperUnipotent n F) :
    quotientReflection n F u ∈ upperUnipotent n F := by
  have hi := (upperUnipotent n F).inv_mem hu
  constructor
  · intro i j hji
    rw [quotientReflection_apply, weylLong_conjugate_entry, inverseTranspose_entry]
    exact hi.1 (Fin.rev_lt_rev.mpr hji)
  · intro i
    rw [quotientReflection_apply, weylLong_conjugate_entry, inverseTranspose_entry]
    exact hi.2 i.rev

theorem quotientReflection_mem_iff (g : Langlands.GeneralLinear n F) :
    quotientReflection n F g ∈ upperUnipotent n F ↔ g ∈ upperUnipotent n F := by
  constructor
  · intro h
    simpa only [quotientReflection_involutive] using
      quotientReflection_mem n F _ h
  · exact quotientReflection_mem n F g

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Reflection is continuous with continuous inverse for the actual units topology. -/
def quotientReflectionContinuous :
    Langlands.GeneralLinear n F ≃ₜ* Langlands.GeneralLinear n F where
  toMulEquiv := quotientReflection n F
  continuous_toFun := (continuous_const.mul (continuous_inverseTranspose n F)).mul
    continuous_const
  continuous_invFun := (continuous_inverseTranspose n F).comp
    ((continuous_const.mul continuous_id).mul continuous_const)

/-- The genuine quotient homeomorphism on left upper-unipotent cosets. -/
def quotientReflectionHomeomorph :
    LeftQuotient (upperUnipotent n F) ≃ₜ LeftQuotient (upperUnipotent n F) :=
  Homeomorph.Quotient.congr (quotientReflectionContinuous n F).toHomeomorph (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ upperUnipotent n F ↔
      quotientReflection n F y * (quotientReflection n F x)⁻¹ ∈ upperUnipotent n F
    rw [← map_inv, ← map_mul, quotientReflection_mem_iff])

@[simp] theorem quotientReflectionHomeomorph_mk (g : Langlands.GeneralLinear n F) :
    quotientReflectionHomeomorph n F (Quotient.mk _ g) =
      Quotient.mk _ (quotientReflection n F g) := rfl

@[simp] theorem quotientReflectionHomeomorph_involutive
    (q : LeftQuotient (upperUnipotent n F)) :
    quotientReflectionHomeomorph n F (quotientReflectionHomeomorph n F q) = q := by
  induction q using Quotient.inductionOn with
  | h g => simp only [quotientReflectionHomeomorph_mk, quotientReflection_involutive]

/-- Reflection conjugates right translation by `g` to translation by its reflection. -/
theorem quotientReflectionHomeomorph_rightTranslate (g : Langlands.GeneralLinear n F)
    (q : LeftQuotient (upperUnipotent n F)) :
    quotientReflectionHomeomorph n F (rightTranslate _ g q) =
      rightTranslate _ (quotientReflection n F g) (quotientReflectionHomeomorph n F q) := by
  induction q using Quotient.inductionOn with
  | h x => simp only [rightTranslate_mk, quotientReflectionHomeomorph_mk, map_mul]

variable [MeasurableSpace (LeftQuotient (upperUnipotent n F))]
  [BorelSpace (LeftQuotient (upperUnipotent n F))]

/-- Transport the primed quotient measure in the stated lower-right coordinates. -/
def reflectedQuotientMeasure (ν : Measure (LeftQuotient (upperUnipotent n F))) :
    Measure (LeftQuotient (upperUnipotent n F)) :=
  Measure.map (quotientReflectionHomeomorph n F) ν

@[simp] theorem reflectedQuotientMeasure_involutive
    (ν : Measure (LeftQuotient (upperUnipotent n F))) :
    reflectedQuotientMeasure n F (reflectedQuotientMeasure n F ν) = ν := by
  rw [reflectedQuotientMeasure, reflectedQuotientMeasure,
    Measure.map_map (quotientReflectionHomeomorph n F).continuous.measurable
      (quotientReflectionHomeomorph n F).continuous.measurable]
  have he : quotientReflectionHomeomorph n F ∘ quotientReflectionHomeomorph n F = id := by
    funext q
    exact quotientReflectionHomeomorph_involutive n F q
  rw [he, Measure.map_id]

theorem reflectedQuotientMeasure_injective :
    Function.Injective (reflectedQuotientMeasure n F) := by
  intro ν η h
  have hh := congrArg (reflectedQuotientMeasure n F) h
  simpa only [reflectedQuotientMeasure_involutive] using hh

theorem reflectedQuotientMeasure_ne_zero_iff
    (ν : Measure (LeftQuotient (upperUnipotent n F))) :
    reflectedQuotientMeasure n F ν ≠ 0 ↔ ν ≠ 0 :=
  Measure.map_ne_zero_iff (quotientReflectionHomeomorph n F).continuous.measurable.aemeasurable

theorem reflectedQuotientMeasure_regular
    (ν : Measure (LeftQuotient (upperUnipotent n F))) [ν.Regular] :
    (reflectedQuotientMeasure n F ν).Regular :=
  Measure.Regular.map (quotientReflectionHomeomorph n F)

theorem integral_reflectedQuotientMeasure
    (ν : Measure (LeftQuotient (upperUnipotent n F)))
    (f : LeftQuotient (upperUnipotent n F) → ℂ) :
    (∫ q, f q ∂reflectedQuotientMeasure n F ν) =
      ∫ q, f (quotientReflectionHomeomorph n F q) ∂ν :=
  integral_map_equiv (quotientReflectionHomeomorph n F).toMeasurableEquiv f

theorem integrable_reflectedQuotientMeasure_iff
    (ν : Measure (LeftQuotient (upperUnipotent n F)))
    (f : LeftQuotient (upperUnipotent n F) → ℂ) :
    Integrable f (reflectedQuotientMeasure n F ν) ↔
      Integrable (fun q => f (quotientReflectionHomeomorph n F q)) ν :=
  integrable_map_equiv (quotientReflectionHomeomorph n F).toMeasurableEquiv f

/-- A right-invariant quotient measure remains right-invariant under reflection. -/
theorem reflectedQuotientMeasure_right_invariant
    (ν : Measure (LeftQuotient (upperUnipotent n F)))
    (hν : ∀ g : Langlands.GeneralLinear n F,
      MeasurePreserving (rightTranslate (upperUnipotent n F) g) ν ν)
    (g : Langlands.GeneralLinear n F) :
    MeasurePreserving (rightTranslate (upperUnipotent n F) g)
      (reflectedQuotientMeasure n F ν) (reflectedQuotientMeasure n F ν) := by
  refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
  rw [reflectedQuotientMeasure, Measure.map_map
    (rightTranslate _ g).continuous.measurable
    (quotientReflectionHomeomorph n F).continuous.measurable]
  have he : rightTranslate (upperUnipotent n F) g ∘ quotientReflectionHomeomorph n F =
      quotientReflectionHomeomorph n F ∘
        rightTranslate (upperUnipotent n F) (quotientReflection n F g) := by
    funext q
    simp only [Function.comp_apply, quotientReflectionHomeomorph_rightTranslate,
      quotientReflection_involutive]
  rw [he, ← Measure.map_map (quotientReflectionHomeomorph n F).continuous.measurable
    (rightTranslate _ _).continuous.measurable, (hν _).map_eq]

/-- The exact quotient-measure equation, without an existence assertion. -/
def IsQuotientReflectionRelated
    (ν ν' : Measure (LeftQuotient (upperUnipotent n F))) : Prop :=
  ν = reflectedQuotientMeasure n F ν'

theorem isQuotientReflectionRelated_comm
    (ν ν' : Measure (LeftQuotient (upperUnipotent n F))) :
    IsQuotientReflectionRelated n F ν ν' ↔ IsQuotientReflectionRelated n F ν' ν := by
  constructor <;> intro h
  · rw [IsQuotientReflectionRelated, h, reflectedQuotientMeasure_involutive]
  · rw [IsQuotientReflectionRelated, h, reflectedQuotientMeasure_involutive]

end Langlands.Shahidi
