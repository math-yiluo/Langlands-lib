import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Basic

/-! # Ideal intersection tensor-kernel transport -/

universe u v

namespace Langlands.Algebra

/-- An elementary tensor-exactness step derived from the intersection/sum
diagram in the proof of Stacks Project Lemma 10.99.7 (tag 00MK). -/
def IdealTensorIntersectionKernelStatement : Prop :=
  ∀ (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] (a J : Ideal R),
    Function.Injective (LinearMap.lTensor M (a ⊔ J).subtype) →
    LinearMap.ker (LinearMap.lTensor M a.subtype) ≤
      LinearMap.range
        (LinearMap.lTensor M (Submodule.inclusion (inf_le_left : a ⊓ J ≤ a)))

end Langlands.Algebra
