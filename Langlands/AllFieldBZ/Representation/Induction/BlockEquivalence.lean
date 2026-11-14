import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.BlockEquivalence

/-!
# All-field port of `Langlands.Representation.Induction.BlockEquivalence`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.BlockEquivalence` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV uW

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
  {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i)}

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Fin B.length → Type uV} {W : Fin B.length → Type uW}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
  {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i)}

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

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
