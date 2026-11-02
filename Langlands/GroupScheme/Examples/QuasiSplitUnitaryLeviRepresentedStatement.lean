import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLevi
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # The unitary Levi as a represented closed subgroup: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- The Weil-restricted multiplicative group represents the dynamic centralizer,
and its diagonal unitary homomorphism is a closed subgroup. -/
def LeviRepresentedStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      (Dynamic.centralizer (cocharacter b c)).IsRepresentedBy (leviHom b c) ∧
      IsClosedSubgroup (leviHom b c)

end Langlands.GroupScheme.QuasiSplitUnitary
