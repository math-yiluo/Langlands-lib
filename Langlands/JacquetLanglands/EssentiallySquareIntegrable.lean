import Langlands.JacquetLanglands.DivisionUnits
import Langlands.Representation.Classification.Essential
import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Langlands.Representation.Twist.AdmissibilityProof
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Essentially square-integrable representations of `GL_n(F)`

For a nonarchimedean local field `F`, square-integrability modulo the center of a
representation of `GL_n(F)`, for every Borel Haar measure on `GL_n(F) / Z`, and essential
square-integrability: some real power `|det|^{-s}` twist is square-integrable modulo the
center.
-/

noncomputable section

open scoped NNReal
open MeasureTheory

namespace Langlands.JacquetLanglands

universe u uV uW

section Norm

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)

/-- The character `g ↦ |det g|` of `GL_n(F)`, for the residue-normalized absolute value of
`F`, with values in the positive real units. -/
def determinantNorm : GeneralLinear n F →* ℝ≥0ˣ :=
  (Plancherel.fieldNormUnits F).comp GeneralLinear.determinant

@[simp]
theorem determinantNorm_coe (g : GeneralLinear n F) :
    ((determinantNorm F n g : ℝ≥0) : ℝ) =
      LocalField.residueNormalizedAbsoluteValue F (GeneralLinear.determinant g : F) :=
  rfl

/-- `|det|` is locally constant on `GL_n(F)`. -/
theorem determinantNorm_isLocallyConstant : IsLocallyConstant (determinantNorm F n) :=
  (Plancherel.fieldNormUnits_isLocallyConstant F).comp_continuous
    Matrix.GeneralLinearGroup.continuous_det

/-- The kernel of `|det|` is an open subgroup of `GL_n(F)`. -/
theorem isOpen_determinantNorm_ker : IsOpen ((determinantNorm F n).ker : Set (GeneralLinear n F)) :=
  (determinantNorm_isLocallyConstant F n).isOpen_fiber 1

end Norm

section SquareIntegrable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable (F n) in
/-- The Borel σ-algebra of the central quotient `GL_n(F) / Z`. -/
abbrev centralQuotientMeasurableSpace :
    MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) :=
  borel _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
variable (F n) in
theorem centralQuotientBorelSpace :
    letI := centralQuotientMeasurableSpace F n
    BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) := by
  let := centralQuotientMeasurableSpace F n
  exact ⟨rfl⟩

variable (F n) in
/-- The central quotient carries a Haar measure, so the predicates below, which quantify
over all of them, are not vacuous. -/
theorem exists_isHaarMeasure_centralQuotient :
    letI := centralQuotientMeasurableSpace F n
    ∃ μ : Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)),
      μ.IsHaarMeasure := by
  have := generalLinear_locallyCompactSpace F n
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  exact ⟨Measure.haarMeasure (Classical.arbitrary _), inferInstance⟩

/-- Square-integrability modulo the center of a representation of `GL_n(F)`, for every
Borel Haar measure on the central quotient `GL_n(F) / Z`: the representation is admissible,
has a unitary central character, and its absolute matrix coefficients are square-integrable
on `GL_n(F) / Z`. -/
def IsSquareIntegrable (ρ : Representation ℂ (GeneralLinear n F) V) : Prop :=
  letI := centralQuotientMeasurableSpace F n
  haveI := centralQuotientBorelSpace F n
  ∀ (μ : Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)))
    [μ.IsHaarMeasure], IsSquareIntegrableModCenter ρ μ

/-- Essential square-integrability: `ρ = |det|^s ⊗ ρ₀` for a real `s` and a representation
`ρ₀` that is square-integrable modulo the center. -/
def IsEssentiallySquareIntegrable (ρ : Representation ℂ (GeneralLinear n F) V) : Prop :=
  ∃ s : ℝ, IsSquareIntegrable (realPowerTwist (determinantNorm F n) (-s) ρ)

/-- A representation that is square-integrable modulo the center is admissible. -/
theorem IsSquareIntegrable.isAdmissible {ρ : Representation ℂ (GeneralLinear n F) V}
    (h : IsSquareIntegrable ρ) : IsAdmissible ρ := by
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  obtain ⟨μ, hμ⟩ := exists_isHaarMeasure_centralQuotient F n
  exact (h μ).1

/-- An essentially square-integrable representation is admissible. -/
theorem IsEssentiallySquareIntegrable.isAdmissible
    {ρ : Representation ℂ (GeneralLinear n F) V} (h : IsEssentiallySquareIntegrable ρ) :
    IsAdmissible ρ := by
  obtain ⟨s, hs⟩ := h
  have ha := hs.isAdmissible
  rw [← realPowerTwist_cancel_neg (determinantNorm F n) s ρ]
  refine (isAdmissible_twist_iff _ _
    (isOpen_ker_realPowerCharacter _ (isOpen_determinantNorm_ker F n) s)).2 ha

theorem isSquareIntegrable_iff_of_equiv {ρ : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear n F) W} (e : ρ.Equiv σ) :
    IsSquareIntegrable ρ ↔ IsSquareIntegrable σ := by
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  exact forall_congr' fun μ => forall_congr' fun _ =>
    isSquareIntegrableModCenter_iff_of_equiv e μ

theorem isEssentiallySquareIntegrable_iff_of_equiv
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear n F) W} (e : ρ.Equiv σ) :
    IsEssentiallySquareIntegrable ρ ↔ IsEssentiallySquareIntegrable σ :=
  exists_congr fun s =>
    isSquareIntegrable_iff_of_equiv (realPowerTwistEquiv (determinantNorm F n) (-s) e)

/-- A square-integrable representation is essentially square-integrable, with `s = 0`. -/
theorem IsSquareIntegrable.isEssentiallySquareIntegrable
    {ρ : Representation ℂ (GeneralLinear n F) V} (h : IsSquareIntegrable ρ) :
    IsEssentiallySquareIntegrable ρ :=
  ⟨0, by rw [neg_zero, realPowerTwist_zero]; exact h⟩

/-- Real `|det|`-power twists preserve essential square-integrability. -/
theorem IsEssentiallySquareIntegrable.realPowerTwist
    {ρ : Representation ℂ (GeneralLinear n F) V} (h : IsEssentiallySquareIntegrable ρ)
    (t : ℝ) : IsEssentiallySquareIntegrable (realPowerTwist (determinantNorm F n) t ρ) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s + t, ?_⟩
  rw [← realPowerTwist_add]
  have he : -(s + t) + t = -s := by ring
  rw [he]
  exact hs

end SquareIntegrable

section RankOne

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `GL_1(F)` is commutative, so its center is everything. -/
theorem mem_center_generalLinear_one (g : GeneralLinear 1 F) :
    g ∈ Subgroup.center (GeneralLinear 1 F) := by
  refine Subgroup.mem_center_iff.mpr fun h => ?_
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The central quotient of `GL_1(F)` has one point. -/
theorem subsingleton_centralQuotient_one :
    Subsingleton (GeneralLinear 1 F ⧸ Subgroup.center (GeneralLinear 1 F)) := by
  refine ⟨fun q q' => ?_⟩
  induction q using QuotientGroup.induction_on with | H g => ?_
  induction q' using QuotientGroup.induction_on with | H g' => ?_
  exact QuotientGroup.eq.mpr (mem_center_generalLinear_one F _)

/-- The trivial representation of `GL_1(F)` on `ℂ` is square-integrable modulo the center:
the central quotient is a point. -/
theorem isSquareIntegrable_trivial_one :
    IsSquareIntegrable (Representation.trivial ℂ (GeneralLinear 1 F) ℂ) := by
  let := centralQuotientMeasurableSpace F 1
  have := centralQuotientBorelSpace F 1
  have hsub := subsingleton_centralQuotient_one F
  intro μ _
  have hsmooth : IsSmooth (Representation.trivial ℂ (GeneralLinear 1 F) ℂ) :=
    fun v => ⟨⊤, fun k => rfl⟩
  refine ⟨⟨hsmooth, fun _ => inferInstance⟩, ?_⟩
  let c : UnitaryCentralCharacter (Representation.trivial ℂ (GeneralLinear 1 F) ℂ) :=
    { character := 1
      isOpen_ker := by rw [MonoidHom.ker_one]; exact isOpen_univ
      norm_eq_one := fun _ => by simp
      acts := fun _ v => by simp }
  refine ⟨c, fun ℓ v => ?_⟩
  have : IsFiniteMeasure μ := inferInstance
  have hc : c.coefficientNorm (ℓ : Module.Dual ℂ ℂ) v =
      fun _ => ‖(ℓ : Module.Dual ℂ ℂ) v‖ := by
    funext q
    induction q using QuotientGroup.induction_on with | H g => ?_
    rfl
  rw [hc]
  exact memLp_const _

/-- Nonvacuity on concrete data: the trivial representation of `GL_1(F)` is essentially
square-integrable. -/
theorem isEssentiallySquareIntegrable_trivial_one :
    IsEssentiallySquareIntegrable (Representation.trivial ℂ (GeneralLinear 1 F) ℂ) :=
  (isSquareIntegrable_trivial_one F).isEssentiallySquareIntegrable

end RankOne

end Langlands.JacquetLanglands
