import Langlands.Shimura.Unitary.ImaginaryQuadraticTensorFactor
import Langlands.Shimura.Unitary.ImaginaryQuadraticModuleNaturality

/-! # Semilinear maps of the actual imaginary quadratic tensor factors -/

noncomputable section

open NumberField Algebra
open scoped TensorProduct

set_option autoImplicit false

universe u v w w' z z'

namespace Langlands.Shimura.ImaginaryQuadratic

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  (R : Type w) [CommRing R] [Algebra K R] [Algebra ℚ R]
  [IsScalarTower ℚ K R]
  (R' : Type w') [CommRing R'] [Algebra K R'] [Algebra ℚ R']
  [IsScalarTower ℚ K R']
  (M : Type z) [AddCommGroup M] [Module R M] [Module ℚ M]
  [IsScalarTower ℚ R M]
  (M' : Type z') [AddCommGroup M'] [Module R' M'] [Module ℚ M']
  [IsScalarTower ℚ R' M']
  (ρ : L →+* Module.End R M) (ρ' : L →+* Module.End R' M')
  (f : R →ₐ[K] R') (F : M →ₛₗ[f.toRingHom] M')
  (hF : ∀ (t : L) (m : M), F (ρ t m) = ρ' t (F m))
  (conjugate : Bool)

/-- The actual map of coordinate scalar-extension modules induced by a semilinear
field-action intertwiner. -/
def tensorFactorMap :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := tensorModule L R' M' ρ'
    letI := factorAlgebra L K R' conjugate
    letI := tensorModuleTower L R' M' ρ'
    letI := factorAlgebraTower L K R' conjugate
    R ⊗[R ⊗[ℚ] L] M →ₛₗ[f.toRingHom] R' ⊗[R' ⊗[ℚ] L] M' := by
  letI := tensorModule L R M ρ
  letI := factorAlgebra L K R conjugate
  letI := tensorModuleTower L R M ρ
  letI := factorAlgebraTower L K R conjugate
  letI := tensorModule L R' M' ρ'
  letI := factorAlgebra L K R' conjugate
  letI := tensorModuleTower L R' M' ρ'
  letI := factorAlgebraTower L K R' conjugate
  exact (tensorFactorEquiv L K R' M' ρ' conjugate).symm.toLinearMap.comp
    ((eigenmoduleMap L K R R' M M' ρ ρ' f F hF conjugate).comp
      (tensorFactorEquiv L K R M ρ conjugate).toLinearMap)

/-- The constructed comparison commutes with the induced actual tensor map. -/
theorem tensorFactorEquiv_naturality
    (x : letI := tensorModule L R M ρ
      letI := factorAlgebra L K R conjugate
      R ⊗[R ⊗[ℚ] L] M) :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := tensorModule L R' M' ρ'
    letI := factorAlgebra L K R' conjugate
    letI := tensorModuleTower L R' M' ρ'
    letI := factorAlgebraTower L K R' conjugate
    tensorFactorEquiv L K R' M' ρ' conjugate
        (tensorFactorMap L K R R' M M' ρ ρ' f F hF conjugate x) =
      eigenmoduleMap L K R R' M M' ρ ρ' f F hF conjugate
        (tensorFactorEquiv L K R M ρ conjugate x) := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := tensorModule L R' M' ρ'
  let := factorAlgebra L K R' conjugate
  let := tensorModuleTower L R' M' ρ'
  let := factorAlgebraTower L K R' conjugate
  exact (tensorFactorEquiv L K R' M' ρ' conjugate).apply_symm_apply _

/-- The tensor-factor map is the canonical map on both actual tensor factors. -/
@[simp]
theorem tensorFactorMap_tmul (r : R) (m : M) :
    letI := tensorModule L R M ρ
    letI := factorAlgebra L K R conjugate
    letI := tensorModuleTower L R M ρ
    letI := factorAlgebraTower L K R conjugate
    letI := tensorModule L R' M' ρ'
    letI := factorAlgebra L K R' conjugate
    letI := tensorModuleTower L R' M' ρ'
    letI := factorAlgebraTower L K R' conjugate
    tensorFactorMap L K R R' M M' ρ ρ' f F hF conjugate
        (r ⊗ₜ[R ⊗[ℚ] L] m) = f r ⊗ₜ[R' ⊗[ℚ] L] F m := by
  let := tensorModule L R M ρ
  let := factorAlgebra L K R conjugate
  let := tensorModuleTower L R M ρ
  let := factorAlgebraTower L K R conjugate
  let := tensorModule L R' M' ρ'
  let := factorAlgebra L K R' conjugate
  let := tensorModuleTower L R' M' ρ'
  let := factorAlgebraTower L K R' conjugate
  apply (tensorFactorEquiv L K R' M' ρ' conjugate).injective
  rw [tensorFactorEquiv_naturality]
  apply Subtype.ext
  change F ((tensorFactorEquiv L K R M ρ conjugate
    (r ⊗ₜ[R ⊗[ℚ] L] m)).val) = _
  rw [tensorFactorEquiv_tmul, tensorFactorEquiv_tmul, F.map_smulₛₗ,
    moduleProjector_naturality L K R R' M M' ρ ρ' f F hF]
  rfl

end Langlands.Shimura.ImaginaryQuadratic
