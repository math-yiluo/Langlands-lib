import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Completed projective tensor products of nonarchimedean normed algebras -/

universe u

open scoped TensorProduct

namespace Langlands.Analysis

/-- Over a complete nontrivially normed ultrametric field `F`, the algebraic
tensor product of two ultrametric normed commutative `F`-algebras embeds, by an
injective `F`-algebra map that is contractive on pure tensors, into a complete
ultrametric normed commutative `F`-algebra. This records that the projective
tensor seminorm is a norm (Gruson–van der Put, Lemma 5.2(2)), so that the
completed tensor product contains the algebraic one. -/
def NonarchimedeanCompletedTensorStatement : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (E : Type u) [NormedCommRing E] [NormedAlgebra F E] [IsUltrametricDist E]
    (E' : Type u) [NormedCommRing E'] [NormedAlgebra F E'] [IsUltrametricDist E'],
    ∃ (W : Type u) (_ : NormedCommRing W) (_ : NormedAlgebra F W)
      (_ : IsUltrametricDist W) (_ : CompleteSpace W)
      (τ : E ⊗[F] E' →ₐ[F] W),
      Function.Injective τ ∧ ∀ (e : E) (e' : E'), ‖τ (e ⊗ₜ[F] e')‖ ≤ ‖e‖ * ‖e'‖

end Langlands.Analysis
