import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.MatrixCoefficient.LawsProof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic.Ring

/-!
# Hermitian products of matrix coefficients on the central quotient

The carrier is an arbitrary complex module. A prescribed actual unitary
central character makes a conjugate-first product descend to `G / Z(G)`.
-/

noncomputable section

namespace Langlands
namespace UnitaryCentralCharacter

universe uG uV

variable {G : Type uG} {V : Type uV}
variable [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} (c : UnitaryCentralCharacter ρ)

include c in
theorem matrixCoefficientProduct_mul_center (ℓ : Module.Dual ℂ V)
    (u v : V) (g : G) (z : Subgroup.center G) :
    (starRingEnd ℂ) (matrixCoefficient ρ ℓ u (g * z)) *
        matrixCoefficient ρ ℓ v (g * z) =
      (starRingEnd ℂ) (matrixCoefficient ρ ℓ u g) *
        matrixCoefficient ρ ℓ v g := by
  have hz : (starRingEnd ℂ) (c.character z : ℂ) * (c.character z : ℂ) = 1 := by
    rw [Complex.conj_mul', c.norm_eq_one]
    norm_num
  rw [c.matrixCoefficient_mul_center, c.matrixCoefficient_mul_center, map_mul]
  calc
    _ = ((starRingEnd ℂ) (c.character z : ℂ) * (c.character z : ℂ)) *
        ((starRingEnd ℂ) (matrixCoefficient ρ ℓ u g) *
          matrixCoefficient ρ ℓ v g) := by ring
    _ = _ := by rw [hz, one_mul]

/-- The conjugate-first product of two actual matrix coefficients, descended
to the actual quotient by the center. -/
def coefficientProduct (ℓ : Module.Dual ℂ V) (u v : V) :
    G ⧸ Subgroup.center G → ℂ :=
  Quotient.lift
    (fun g => (starRingEnd ℂ) (matrixCoefficient ρ ℓ u g) *
      matrixCoefficient ρ ℓ v g) (by
      intro a b hab
      have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hab
      have h := c.matrixCoefficientProduct_mul_center ℓ u v a ⟨a⁻¹ * b, hz⟩
      simpa using h.symm)

@[simp] theorem coefficientProduct_mk (ℓ : Module.Dual ℂ V) (u v : V) (g : G) :
    c.coefficientProduct ℓ u v (QuotientGroup.mk g) =
      (starRingEnd ℂ) (matrixCoefficient ρ ℓ u g) *
        matrixCoefficient ρ ℓ v g := rfl

theorem norm_coefficientProduct (ℓ : Module.Dual ℂ V) (u v : V)
    (q : G ⧸ Subgroup.center G) :
    ‖c.coefficientProduct ℓ u v q‖ =
      c.coefficientNorm ℓ u q * c.coefficientNorm ℓ v q := by
  induction q using Quotient.inductionOn
  simp

theorem coefficientProduct_self (ℓ : Module.Dual ℂ V) (u : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ u u q = ((c.coefficientNorm ℓ u q) ^ 2 : ℝ) := by
  induction q using Quotient.inductionOn
  simp [Complex.conj_mul']

theorem coefficientProduct_conj (ℓ : Module.Dual ℂ V) (u v : V)
    (q : G ⧸ Subgroup.center G) :
    (starRingEnd ℂ) (c.coefficientProduct ℓ u v q) =
      c.coefficientProduct ℓ v u q := by
  induction q using Quotient.inductionOn
  simp [mul_comm]

@[simp] theorem coefficientProduct_zero_left (ℓ : Module.Dual ℂ V) (v : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ 0 v q = 0 := by
  induction q using Quotient.inductionOn
  simp [matrixCoefficient]

@[simp] theorem coefficientProduct_zero_right (ℓ : Module.Dual ℂ V) (u : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ u 0 q = 0 := by
  induction q using Quotient.inductionOn
  simp [matrixCoefficient]

theorem coefficientProduct_add_left (ℓ : Module.Dual ℂ V) (u₁ u₂ v : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ (u₁ + u₂) v q =
      c.coefficientProduct ℓ u₁ v q + c.coefficientProduct ℓ u₂ v q := by
  induction q using Quotient.inductionOn
  simp [matrixCoefficient, add_mul]

theorem coefficientProduct_add_right (ℓ : Module.Dual ℂ V) (u v₁ v₂ : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ u (v₁ + v₂) q =
      c.coefficientProduct ℓ u v₁ q + c.coefficientProduct ℓ u v₂ q := by
  induction q using Quotient.inductionOn
  simp [matrixCoefficient, mul_add]

theorem coefficientProduct_smul_left (ℓ : Module.Dual ℂ V) (a : ℂ) (u v : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ (a • u) v q =
      (starRingEnd ℂ) a * c.coefficientProduct ℓ u v q := by
  induction q using Quotient.inductionOn
  simp [matrixCoefficient, mul_assoc]

theorem coefficientProduct_smul_right (ℓ : Module.Dual ℂ V) (a : ℂ) (u v : V)
    (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ u (a • v) q =
      a * c.coefficientProduct ℓ u v q := by
  induction q using Quotient.inductionOn
  simp [matrixCoefficient, mul_left_comm]

theorem coefficientProduct_translate (ℓ : Module.Dual ℂ V) (u v : V)
    (h : G) (q : G ⧸ Subgroup.center G) :
    c.coefficientProduct ℓ (ρ h u) (ρ h v) q =
      c.coefficientProduct ℓ u v (q * QuotientGroup.mk h) := by
  induction q using Quotient.inductionOn
  simp [← QuotientGroup.mk_mul]

theorem coefficientProduct_eq (d : UnitaryCentralCharacter ρ)
    (ℓ : Module.Dual ℂ V) (u v : V) :
    c.coefficientProduct ℓ u v = d.coefficientProduct ℓ u v := by
  funext q
  induction q using Quotient.inductionOn
  rfl

variable [IsTopologicalGroup G]

theorem continuous_coefficientProduct (ℓ : Module.Dual ℂ V) (u v : V)
    (hu : IsSmoothVector ρ u) (hv : IsSmoothVector ρ v) :
    Continuous (c.coefficientProduct ℓ u v) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
  exact ((matrixCoefficient_isLocallyConstant ρ ℓ u hu).continuous.star).mul
    (matrixCoefficient_isLocallyConstant ρ ℓ v hv).continuous

theorem measurable_coefficientProduct
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (ℓ : Module.Dual ℂ V) (u v : V)
    (hu : IsSmoothVector ρ u) (hv : IsSmoothVector ρ v) :
    Measurable (c.coefficientProduct ℓ u v) :=
  (c.continuous_coefficientProduct ℓ u v hu hv).measurable

theorem aestronglyMeasurable_coefficientProduct
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (ℓ : Module.Dual ℂ V) (u v : V)
    (hu : IsSmoothVector ρ u) (hv : IsSmoothVector ρ v)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)) :
    MeasureTheory.AEStronglyMeasurable (c.coefficientProduct ℓ u v) μ :=
  (c.continuous_coefficientProduct ℓ u v hu hv).aestronglyMeasurable

end UnitaryCentralCharacter
end Langlands
