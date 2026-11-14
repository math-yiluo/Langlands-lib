import Langlands.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.Induction.BlockFactors
/-! Actual normalized induction transports a family of representation equivalences. -/

noncomputable section

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW


end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV uW

variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
  {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}

/-- Block equivalences induce an equivalence of actual normalized upper inductions. -/
def normalizedProductInducedEquiv (e : ∀ i, (σ i).Equiv (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).Equiv (T.normalizedProductInduced B τ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.productInducedOfEquiv (T.leviHalfCharacter B) e

@[simp]
theorem normalizedProductInducedEquiv_toIntertwiningMap
    (e : ∀ i, (σ i).Equiv (τ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInducedEquiv B e).toIntertwiningMap =
      T.normalizedProductInducedMap B (fun i => (e i).toIntertwiningMap) := rfl

end Langlands.LocalFieldData
