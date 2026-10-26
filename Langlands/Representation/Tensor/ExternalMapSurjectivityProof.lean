import Langlands.Representation.Tensor.ExternalMapSurjectivityStatement

/-! # Surjectivity of external tensor maps

Lift the coordinates of scaled pure tensors and then add their preimages.
-/

namespace Langlands.FiniteTensor

universe uR uI uG uV uW

variable (R : Type uR) [CommRing R] (ι : Type uI)
variable (H : ι → Type uG) [∀ i, Group (H i)]
variable (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable (W : ι → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

/-- Factorwise surjectivity lifts through the actual external tensor map. -/
theorem externalMapSurjectivity : ExternalMapSurjectivity R ι H V W := by
  intro ρ σ f hf y
  change ∃ x, PiTensorProduct.map (fun i => (f i).toLinearMap) x = y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    choose w hw using fun i => hf i (v i)
    refine ⟨a • PiTensorProduct.tprod R w, ?_⟩
    simp only [map_smul, PiTensorProduct.map_tprod]
    exact congrArg (fun v => a • PiTensorProduct.tprod R v) (funext hw)
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

end Langlands.FiniteTensor
