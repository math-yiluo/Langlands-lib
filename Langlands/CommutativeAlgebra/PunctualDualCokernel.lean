import Langlands.CommutativeAlgebra.PunctualFirstDifferential
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The cokernel of the dual first differential -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Evaluate the dual of a rank-one module at its chosen generator. -/
def rankOneDualEvaluation (e₀ : M ≃ₗ[R] R) : Module.Dual R M ≃ₗ[R] R :=
  e₀.symm.dualMap ≪≫ₗ LinearMap.ringLmapEquivSelf R R R

@[simp]
theorem rankOneDualEvaluation_apply (e₀ : M ≃ₗ[R] R) (φ : Module.Dual R M) :
    rankOneDualEvaluation e₀ φ = φ (e₀.symm 1) := rfl

variable (L : CochainComplex (ModuleCat.{u} R) ℤ) (e₀ : L.X 0 ≃ₗ[R] R)

/-- Evaluation identifies the image of the dual first differential with
the first-differential order ideal. -/
theorem dual_firstDifferential_range :
    (LinearMap.range (L.d 0 1).hom.dualMap).map
        (rankOneDualEvaluation e₀).toLinearMap =
      firstDifferentialOrderIdeal L e₀ := by
  rw [← LinearMap.range_comp]
  rfl

/-- The dual first differential has cokernel the quotient by its order ideal. -/
def firstDifferentialDualCokernelIsoQuotient :
    cokernel (ModuleCat.ofHom (L.d 0 1).hom.dualMap) ≅
      ModuleCat.of R (R ⧸ firstDifferentialOrderIdeal L e₀) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.Quotient.equiv _ _ (rankOneDualEvaluation e₀)
      (dual_firstDifferential_range L e₀)).toModuleIso

/-- If the order ideal is the maximal ideal, the dual first differential
has cokernel the actual residue field, as an `R`-module. -/
def firstDifferentialDualCokernelIsoResidueField [IsLocalRing R]
    (h : firstDifferentialOrderIdeal L e₀ = maximalIdeal R) :
    cokernel (ModuleCat.ofHom (L.d 0 1).hom.dualMap) ≅
      ModuleCat.of R (ResidueField R) :=
  firstDifferentialDualCokernelIsoQuotient L e₀ ≪≫
    (Submodule.quotEquivOfEq _ _ h).toModuleIso

theorem nonempty_firstDifferentialDualCokernelIsoResidueField [IsLocalRing R]
    (h : firstDifferentialOrderIdeal L e₀ = maximalIdeal R) :
    Nonempty (cokernel (ModuleCat.ofHom (L.d 0 1).hom.dualMap) ≅
      ModuleCat.of R (ResidueField R)) :=
  ⟨firstDifferentialDualCokernelIsoResidueField L e₀ h⟩

end Langlands.CommutativeAlgebra
