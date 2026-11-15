import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Tensor products of semisimple representations of abstract groups in characteristic zero
(statement) -/

universe u v w₁ w₂

namespace Langlands.GroupScheme

/-- **Tensor products of semisimple representations of an abstract group in characteristic
zero** (Milne, *Algebraic Groups* (2017), Corollary 22.45, after Chevalley). Let `G` be an
abstract group and let `ρ`, `σ` be representations of `G` on finite-dimensional vector spaces
`V`, `W` over a field `k` of characteristic zero. If `ρ` and `σ` are semisimple, then so is the
tensor product representation `ρ.tprod σ` of `G` on `V ⊗[k] W`, `g ↦ ρ g ⊗ σ g`.

Semisimple is Mathlib's `Representation.IsSemisimpleRepresentation`: every subrepresentation
(`G`-stable subspace) has a complementary subrepresentation. For finite-dimensional
representations this is equivalent to being the sum of the simple subrepresentations. -/
def CharZeroAbstractGroupTensorSemisimpleStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : Type v) [Group G]
    (V : Type w₁) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Type w₂) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
      (ρ.tprod σ).IsSemisimpleRepresentation

end Langlands.GroupScheme
