import Langlands.LocalFactor.NonabelianBrauerSystem
import Langlands.LocalFactor.NonabelianBrauerKernelProof

/-! # Existence of actual common-closure local-constant systems

Proof of `Langlands.LocalFactor.NonabelianSystem.Exists`: the published
specialization `NonabelianBrauer.exists_of_kernelCompatibilityStatement` applied to
the published proof `NonabelianBrauer.kernelCompatibilityStatement` of the
Brauer-kernel compatibility statement.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

/-- **Existence of local-constant systems in one common algebraic closure.** For every
prime `p`, every p-adic field `F`, every representation universe `uV` and every supplied
reciprocity family `e`, if `e` satisfies `NormalizedReciprocity F e`, then there is an
actual unit-valued assignment on the continuous exact virtual groups of all finite
intermediate fields satisfying the additive, Haar-scaling, degree-zero induction and
rank-one laws simultaneously. -/
theorem exists_system {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : CommonClosure.ReciprocityFamily F) :
    NonabelianSystem.Exists.{uF, uV} F e :=
  NonabelianBrauer.exists_of_kernelCompatibilityStatement F e
    NonabelianBrauer.kernelCompatibilityStatement.{uF, uV}

end Langlands.LocalFactor.NonabelianSystem
