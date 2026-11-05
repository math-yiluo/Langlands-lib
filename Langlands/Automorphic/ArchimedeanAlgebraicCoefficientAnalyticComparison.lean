import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticCovariance
import Langlands.GroupScheme.MatrixRepresentationProductDifferentialComparison

/-! # Actual analytic and algebraic archimedean coefficient comparison -/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

omit [NumberField F] in
/-- The genuine real Frechet differential equals the algebraic coefficient
action, by the published comparison for the original scheme representation. -/
theorem analyticRealDifferential_eq_lie (X : RealLieAlgebra F n) (v : Space e ρ) :
    analyticRealDifferential e ρ X v = ⁅(1 : ℂ) ⊗ₜ[ℝ] X, v⁆ :=
  analyticRealDifferential_eq_lie_of_comparison e ρ
    (ρ.analyticProductDifferentialComparison (B := ℂ)) X v

omit [NumberField F] in
/-- Equality of the two independently constructed complexified actions on
every original coefficient vector. -/
theorem analyticComplexDifferential_eq_lie (Z : ComplexLieAlgebra F n) (v : Space e ρ) :
    analyticComplexDifferential e ρ Z v = ⁅Z, v⁆ := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    rw [analyticComplexDifferential_tmul]
    change z • analyticRealDifferential e ρ X v = ⁅z ⊗ₜ[ℝ] X, v⁆
    rw [analyticRealDifferential_eq_lie]
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, _root_.smul_lie]
  | add Z W hZ hW =>
    simp only [map_add, LinearMap.add_apply, add_lie, hZ, hW]

/-- The actual analytic and algebraic Lie homomorphisms coincide. -/
theorem analyticComplexLieAction_eq :
    analyticComplexLieAction e ρ = lieAction e ρ := by
  apply LieHom.ext
  intro Z
  apply LinearMap.ext
  intro v
  exact analyticComplexDifferential_eq_lie e ρ Z v

/-- All original coefficient vectors, with both actual Lie actions identified. -/
def analyticAlgebraicLieEquiv :
    AnalyticSpace e ρ ≃ₗ⁅ℂ, ComplexLieAlgebra F n⁆ Space e ρ :=
  { analyticCoordinates e ρ with
    map_lie' := by
      intro Z v
      exact (analyticCoordinates_lie e ρ Z v).trans
        (analyticComplexDifferential_eq_lie e ρ Z (analyticCoordinates e ρ v)) }

@[simp]
theorem analyticAlgebraicLieEquiv_apply (v : AnalyticSpace e ρ) :
    analyticAlgebraicLieEquiv e ρ v = analyticCoordinates e ρ v := rfl

/-- The same underlying coordinate identity also preserves the original full
archimedean group representation. -/
def analyticAlgebraicRepresentationEquiv :
    (analyticRepresentation e ρ).Equiv (representation e ρ) :=
  Representation.Equiv.mk (analyticCoordinates e ρ) (fun g => by
    apply LinearMap.ext
    intro v
    rfl)

@[simp]
theorem analyticAlgebraicRepresentationEquiv_apply (v : AnalyticSpace e ρ) :
    analyticAlgebraicRepresentationEquiv e ρ v = analyticAlgebraicLieEquiv e ρ v := rfl

/-- The same map preserves the full compact restriction. -/
def analyticAlgebraicCompactEquiv :
    (analyticCompactRepresentation e ρ).Equiv (compactRepresentation e ρ) :=
  Representation.Equiv.mk (analyticCoordinates e ρ) (fun k => by
    apply LinearMap.ext
    intro v
    rfl)

@[simp]
theorem analyticAlgebraicCompactEquiv_apply (v : AnalyticSpace e ρ) :
    analyticAlgebraicCompactEquiv e ρ v = analyticAlgebraicLieEquiv e ρ v := rfl

theorem analyticAlgebraicReduced_lie (X : ReducedComplexLieAlgebra F n)
    (v : AnalyticSpace e ρ) :
    analyticAlgebraicLieEquiv e ρ (analyticReducedLieAction e ρ X v) =
      reducedLieAction e ρ X (analyticAlgebraicLieEquiv e ρ v) :=
  (analyticAlgebraicLieEquiv e ρ).map_lie (reducedComplexInclusion F n X) v

theorem analyticAlgebraicCompact_lie (X : CompactComplexLieAlgebra F n)
    (v : AnalyticSpace e ρ) :
    analyticAlgebraicLieEquiv e ρ (analyticCompactLieAction e ρ X v) =
      compactLieAction e ρ X (analyticAlgebraicLieEquiv e ρ v) :=
  (analyticAlgebraicLieEquiv e ρ).map_lie (compactComplexInclusion F n X) v

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
