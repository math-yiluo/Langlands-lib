import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyInverseAssembly
import Langlands.Geometry.FormalGroup.IsogenyDual

/-! # Inverses of actual local quasi-isogenies -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]

/-- Every actual local quasi-isogeny has the unique actual two-sided
section inverse with the reverse local scalar-isogeny condition. -/
theorem localQuasiIsogenyInverse (F : Type v) [Field F] [Algebra O F]
    (π : O) (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :
    LocalQuasiIsogenyInverseStatement F π M N :=
  localQuasiIsogenyInverse_of_integralDuals π
    (fun _ hM hN _ hf => hf.exists_dual hM hN)

end Langlands.FormalGroup.ModuleLaw
