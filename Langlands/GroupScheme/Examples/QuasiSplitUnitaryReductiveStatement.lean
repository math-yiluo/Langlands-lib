import Langlands.GroupScheme.Examples.QuasiSplitUnitary
import Langlands.GroupScheme.Reductive.Basic

/-! # The quasi-split unitary group `U(1,1)` is connected reductive: statement -/

universe u

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- For a nontrivial conjugation `c`, the group `U(1,1)` over `Spec F` is a connected reductive
group. -/
def IsConnectedReductiveStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl → IsConnectedReductive (groupScheme b c)

end Langlands.GroupScheme.QuasiSplitUnitary
