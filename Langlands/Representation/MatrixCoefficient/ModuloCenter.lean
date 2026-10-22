import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Group.Measure

/-!
# Absolute matrix coefficients modulo the center

The complex representation carrier has no topology. A genuine unitary central
character makes the absolute value of each coefficient a function on `G / Z(G)`.
-/

noncomputable section

namespace Langlands

universe uG uV

variable {G : Type uG} {V : Type uV}
variable [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

/-- A prescribed smooth unitary central character, with its actual scalar action.
Existence of this datum for a representation is not asserted. -/
structure UnitaryCentralCharacter (ρ : Representation ℂ G V) where
  character : Subgroup.center G →* ℂˣ
  isOpen_ker : IsOpen (character.ker : Set (Subgroup.center G))
  norm_eq_one : ∀ z, ‖(character z : ℂ)‖ = 1
  acts : ∀ (z : Subgroup.center G) (v : V), ρ z v = (character z : ℂ) • v

namespace UnitaryCentralCharacter

variable {ρ : Representation ℂ G V} (c : UnitaryCentralCharacter ρ)

theorem matrixCoefficient_mul_center (ℓ : Module.Dual ℂ V) (v : V)
    (g : G) (z : Subgroup.center G) :
    matrixCoefficient ρ ℓ v (g * z) =
      (c.character z : ℂ) * matrixCoefficient ρ ℓ v g := by
  change ℓ (ρ (g * z) v) = (c.character z : ℂ) * ℓ (ρ g v)
  rw [map_mul, Module.End.mul_apply, c.acts, map_smul, map_smul]
  rfl

include c in
theorem norm_matrixCoefficient_mul_center (ℓ : Module.Dual ℂ V) (v : V)
    (g : G) (z : Subgroup.center G) :
    ‖matrixCoefficient ρ ℓ v (g * z)‖ = ‖matrixCoefficient ρ ℓ v g‖ := by
  rw [c.matrixCoefficient_mul_center, norm_mul, c.norm_eq_one, one_mul]

/-- The absolute matrix coefficient on the actual quotient by the center.
Well-definedness is proved from the scalar action and unitary character. -/
def coefficientNorm (ℓ : Module.Dual ℂ V) (v : V) :
    G ⧸ Subgroup.center G → ℝ :=
  Quotient.lift (fun g => ‖matrixCoefficient ρ ℓ v g‖) (by
    intro a b hab
    have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hab
    have h := c.norm_matrixCoefficient_mul_center ℓ v a ⟨a⁻¹ * b, hz⟩
    simpa using h.symm)

@[simp] theorem coefficientNorm_mk (ℓ : Module.Dual ℂ V) (v : V) (g : G) :
    c.coefficientNorm ℓ v (QuotientGroup.mk g) = ‖matrixCoefficient ρ ℓ v g‖ := rfl

theorem coefficientNorm_nonneg (ℓ : Module.Dual ℂ V) (v : V)
    (q : G ⧸ Subgroup.center G) : 0 ≤ c.coefficientNorm ℓ v q := by
  induction q using Quotient.inductionOn
  exact norm_nonneg _

/-- The descended norm does not depend on the chosen central-character datum. -/
theorem coefficientNorm_eq (d : UnitaryCentralCharacter ρ)
    (ℓ : Module.Dual ℂ V) (v : V) :
    c.coefficientNorm ℓ v = d.coefficientNorm ℓ v := by
  funext q
  induction q using Quotient.inductionOn
  rfl

end UnitaryCentralCharacter

/-- Square-integrability modulo the center for an admissible complex
representation and a specified Haar measure on the actual central quotient.
The quantification is over smooth-dual functionals and all representation vectors. -/
def IsSquareIntegrableModCenter
    [IsTopologicalGroup G]
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  IsAdmissible ρ ∧ ∃ c : UnitaryCentralCharacter ρ,
    ∀ (ℓ : SmoothDual ρ) (v : V), MeasureTheory.MemLp (c.coefficientNorm ℓ v) 2 μ

end Langlands
