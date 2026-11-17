import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Rosenlicht's tensor-unit statement

The affine coordinate-ring form of Milne, *Algebraic Groups* (2017),
Proposition 12.48. See the paired Markdown for the translation.
-/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Every unit in the tensor product of two finite-type domains over an
algebraically closed field is a pure tensor of units. -/
def RosenlichtTensorUnitsStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A]
    (B : Type w) [CommRing B] [Algebra k B] [IsDomain B] [Algebra.FiniteType k B]
    (z : (A ⊗[k] B)ˣ),
    ∃ (a : Aˣ) (b : Bˣ), (z : A ⊗[k] B) = (a : A) ⊗ₜ[k] (b : B)

end Langlands.Algebra
