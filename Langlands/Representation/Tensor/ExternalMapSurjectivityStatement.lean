import Langlands.Representation.Tensor.Finite

/-! # Surjectivity of the actual external tensor map

This proposition records a derived algebraic property of `externalMap`.
-/

namespace Langlands.FiniteTensor

universe uR uI uG uV uW

variable (R : Type uR) [CommRing R] (ι : Type uI)
variable (H : ι → Type uG) [∀ i, Group (H i)]
variable (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable (W : ι → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

/-- Surjective factor intertwiners induce a surjective actual external tensor
map. The algebraic assertion includes empty and arbitrary index types. -/
def ExternalMapSurjectivity : Prop :=
  ∀ (ρ : ∀ i, Representation R (H i) (V i))
    (σ : ∀ i, Representation R (H i) (W i))
    (f : ∀ i, (ρ i).IntertwiningMap (σ i)),
    (∀ i, Function.Surjective (f i)) →
      Function.Surjective (externalMap f)

end Langlands.FiniteTensor
