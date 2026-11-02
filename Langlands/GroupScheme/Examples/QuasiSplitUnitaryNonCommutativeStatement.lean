import Langlands.GroupScheme.Examples.QuasiSplitUnitary

/-! # The quasi-split unitary group `U(1,1)` is not commutative: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- For a nontrivial conjugation `c`, the group `U(1,1)` has two points over `Spec F` itself
that do not commute. -/
def NonCommutativeStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      ∃ g h : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (groupScheme b c).X, g * h ≠ h * g

end Langlands.GroupScheme.QuasiSplitUnitary
