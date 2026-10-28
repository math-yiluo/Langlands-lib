import Langlands.Shimura.PEL.TraceSimilitudes
import Langlands.Shimura.PEL.HodgeTraceForm
import Langlands.Shimura.Unitary.Adelic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Scalar-extended and adelic trace-form similitudes -/

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Algebra

/-- Nondegeneracy over a field survives arbitrary commutative scalar extension
for a finite-dimensional vector space. -/
theorem bilinForm_baseChange_nondegenerate
    {F M S : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] [CommRing S] [Algebra F S]
    (ψ : LinearMap.BilinForm F M) (hψ : ψ.Nondegenerate) :
    (ψ.baseChange S).Nondegenerate := by
  classical
  let b := Module.finBasis F M
  have hm :
      LinearMap.BilinForm.toMatrix (b.baseChange S) (ψ.baseChange S) =
        (LinearMap.BilinForm.toMatrix b ψ).map (algebraMap F S) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      LinearMap.BilinForm.baseChange_tmul, one_mul, Matrix.map_apply,
      _root_.Algebra.algebraMap_eq_smul_one]
  have hd : (LinearMap.BilinForm.toMatrix b ψ).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hψ
  have hu : IsUnit
      (LinearMap.BilinForm.toMatrix (b.baseChange S) (ψ.baseChange S)).det := by
    rw [hm]
    change IsUnit ((algebraMap F S).mapMatrix (LinearMap.BilinForm.toMatrix b ψ)).det
    rw [← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hd).map (algebraMap F S)
  exact (LinearMap.BilinForm.nondegenerate_toMatrix_iff (b.baseChange S)).mp
    (Matrix.Nondegenerate.of_det_mem_nonZeroDivisors hu.mem_nonZeroDivisors)

end Langlands.Algebra

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    (S : Type z) [CommRing S] [Algebra ℚ S] (β : Aˣ)

/-- The actual extended trace pairing is nondegenerate over every rational
coefficient algebra, including ones with zero divisors. -/
theorem tracePairingBaseChange_nondegenerate :
    (D.tracePairingBaseChange S β).Nondegenerate := by
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  have : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ E A
  exact Langlands.Algebra.bilinForm_baseChange_nondegenerate
    (D.tracePairing β) (D.tracePairing_nondegenerate β)

variable (hβ : D.involution (β : A) = -(β : A))

/-- The extended inverse-unit trace form realizes the original Harris
involution, through right multiplication and the opposite group. -/
def harrisTraceSimilitudesEquiv :
    (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes (S ⊗[ℚ] A)
        ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹) :=
  PEL.algebraicBilinearEquiv _ _
    ((D.skewTwist β hβ).tracePairingBaseChange_nondegenerate S β⁻¹)
    (D.skewTwist_tracePairingBaseChange_right β hβ S)

@[simp] theorem harrisTraceSimilitudesEquiv_apply
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ)
    (x : S ⊗[ℚ] A) :
    (D.harrisTraceSimilitudesEquiv S β hβ g).val.1 x =
      x * (g.unop.val.1 : S ⊗[ℚ] A) := rfl

@[simp] theorem harrisTraceSimilitudesEquiv_multiplier
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ) :
    PEL.bilinearSimilitudes.multiplier
        ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹)
        (D.harrisTraceSimilitudesEquiv S β hβ g) =
      AlgebraInvolution.Points.multiplier
        D.toSecondKindInvolution.rationalInvolution S g.unop := rfl

/-- The finite adelic specialization uses the actual rational finite adeles. -/
def harrisFiniteAdelicTraceSimilitudesEquiv :
    D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes (Langlands.Global.FiniteAdeles ℚ ⊗[ℚ] A)
        ((D.skewTwist β hβ).tracePairingBaseChange
          (Langlands.Global.FiniteAdeles ℚ) β⁻¹) :=
  D.harrisTraceSimilitudesEquiv (Langlands.Global.FiniteAdeles ℚ) β hβ

end Langlands.Shimura.CentralSimpleUnitaryData
