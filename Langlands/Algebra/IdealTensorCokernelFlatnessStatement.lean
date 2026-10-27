import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs

universe u v w

namespace Langlands.Algebra

/-- A universally ideal-quotient-injective inclusion into a flat module
has flat cokernel. -/
def IdealTensorCokernelFlatnessStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B),
    Module.Flat R B →
    Function.Injective f →
    (∀ I : Ideal R, Function.Injective (LinearMap.lTensor (R ⧸ I) f)) →
    Module.Flat R (B ⧸ LinearMap.range f)

end Langlands.Algebra
