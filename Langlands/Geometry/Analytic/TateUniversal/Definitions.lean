import Langlands.Geometry.Analytic.TateEvaluation.Definitions
import Langlands.Geometry.Analytic.Affinoid

/-! # Coordinates and the continuous linear map of a bounded algebra map -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w}
  [NormedField K] [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]

/-- The continuous linear map underlying an actual bounded algebra homomorphism. -/
def toContinuousLinearMap (f : BoundedAlgHom K A B) : A →L[K] B :=
  f.toAlgHom.toLinearMap.mkContinuous f.bounded.choose f.bounded.choose_spec.2

@[simp]
theorem toContinuousLinearMap_apply (f : BoundedAlgHom K A B) (a : A) :
    f.toContinuousLinearMap a = f a := rfl

theorem continuous (f : BoundedAlgHom K A B) : Continuous f :=
  f.toContinuousLinearMap.continuous

end BoundedAlgHom

namespace StrictTateAlgebra

variable (σ : Type u) (K : Type v) [NormedField K] [IsUltrametricDist K]

/-- A coordinate of the actual Tate algebra. -/
def X (i : σ) : StrictTateAlgebra σ K :=
  monomial σ K (Finsupp.single i 1) 1

theorem norm_X (i : σ) : ‖X σ K i‖ = 1 := by
  rw [X, norm_monomial, norm_one]

end StrictTateAlgebra

end Langlands.Analytic
