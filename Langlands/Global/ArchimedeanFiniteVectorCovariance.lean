import Langlands.Global.ArchimedeanFiniteVectorDifferential
import Langlands.Global.ArchimedeanCovarianceProof

/-! # Full-group covariance of genuine finite-vector differentiation -/

noncomputable section

universe uF uI

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (ι : Type uI) [Fintype ι]

/-- The original right translation intertwines actual vector differentiation
with the actual adjoint action on every complexified Lie vector. -/
theorem vectorSmoothRightAction_finiteVectorSmoothLieAction
    (g : InfiniteAdelicGL F n) (Z : ComplexLieAlgebra F n)
    (f : VectorSmoothFunctions F n (ι → ℂ)) :
    vectorSmoothRightAction F n (ι → ℂ) g (finiteVectorSmoothLieAction F n ι Z f) =
      finiteVectorSmoothLieAction F n ι (complexLieConjugation F n g Z)
        (vectorSmoothRightAction F n (ι → ℂ) g f) := by
  apply Subtype.ext
  funext x i
  change (smoothRightAction F n g
      (complexSmoothLieAction F n Z (finiteVectorSmoothEquiv F n ι f i))).val x =
    (complexSmoothLieAction F n (complexLieConjugation F n g Z)
      (smoothRightAction F n g (finiteVectorSmoothEquiv F n ι f i))).val x
  exact congrArg (fun h : SmoothFunctions F n => h.val x)
    (smoothRightAction_complexSmoothLieAction F n g Z (finiteVectorSmoothEquiv F n ι f i))

end Langlands.Global.ArchimedeanGL
