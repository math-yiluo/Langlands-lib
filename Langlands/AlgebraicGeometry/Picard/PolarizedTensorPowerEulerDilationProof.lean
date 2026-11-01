import Langlands.AlgebraicGeometry.Picard.PolarizedTensorPowerEulerDilationStatement
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof

/-! # Proof of tensor-power and Euler dilation from an actual polarization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Apply a polarization to each tensor factor and flatten the resulting powers. -/
def polarizedTensorPowIso {X : Scheme.{u}} (f : X ⟶ X) (M : X.Modules) (q : ℕ)
    (e : (Scheme.Modules.pullback f).obj M ≅ tensorPow M q) (n : ℕ) :
    tensorPow ((Scheme.Modules.pullback f).obj M) n ≅ tensorPow M (q * n) :=
  tensorPowIso e n ≪≫ tensorPowMulIso M q n

/-- Pull back a tensor power and then apply the powered polarization. -/
def polarizedPullbackTensorPowIso {X : Scheme.{u}} (f : X ⟶ X) (M : X.Modules) (q : ℕ)
    (e : (Scheme.Modules.pullback f).obj M ≅ tensorPow M q) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (tensorPow M n) ≅ tensorPow M (q * n) :=
  actualPullbackTensorPowIso f M n ≪≫ polarizedTensorPowIso f M q e n

/-- Actual polarization dilates tensor exponents and the corresponding Euler values. -/
theorem polarizedTensorPowerEulerDilation :
    PolarizedTensorPowerEulerDilationStatement.{u} := by
  constructor
  · intro X f M q e n
    exact ⟨⟨polarizedTensorPowIso f M q e n⟩,
      ⟨polarizedPullbackTensorPowIso f M q e n⟩⟩
  · intro K _ X s f M q e n
    let E := polarizedTensorPowIso f M q e n
    refine ⟨⟨hasFiniteCohomology_of_iso s E,
      hasFiniteCohomology_of_iso s E.symm⟩, ?_⟩
    intro hF hM
    exact eulerCharacteristic_eq_of_iso s hF hM E

end Langlands.AlgebraicGeometry.Picard
