import Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement
import Langlands.CommutativeAlgebra.IntegralFibre.AwaySplit
import Langlands.CommutativeAlgebra.IntegralFibre.GeometricallyIntegral
import Langlands.CommutativeAlgebra.IntegralFibre.Assembly

/-! # Projectivity of flat algebras with geometrically integral fibres -/

universe u

namespace Langlands.CommutativeAlgebra

open TensorProduct

/-- **Stacks 05FT.** A flat finitely presented algebra with geometrically integral fibres is
projective as a module over its base. -/
theorem integralFibreProjectivity : IntegralFibreProjectivityStatement.{u} := by
  intro R S _ _ _ hfp hflat hGI
  have hS := isDomain_tensor_of_geometricallyIntegral hGI
  exact projective_of_forall_locallySplit_away hS fun s h₁ h₂ ↦ by
    have := h₁
    have := h₂
    exact IntegralFibre.locallySplit_away s hS

end Langlands.CommutativeAlgebra
