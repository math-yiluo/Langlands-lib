import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Langlands.GroupScheme.Dynamic.Basic

/-! # Dynamic subgroups of the quasi-split unitary group: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- The dynamic subgroups for the two opposite hyperbolic cocharacters, including
the descriptions of both unipotent subgroups as images of the root maps. -/
def DynamicStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      Dynamic.parabolic (cocharacter b c) = upperTriangular b c ∧
      Dynamic.centralizer (cocharacter b c) = diagonal b c ∧
      Dynamic.unipotent (cocharacter b c) = upperUnipotent b c ∧
      Dynamic.parabolic (inverseCocharacter b c) = lowerTriangular b c ∧
      Dynamic.centralizer (inverseCocharacter b c) = diagonal b c ∧
      Dynamic.unipotent (inverseCocharacter b c) = lowerUnipotent b c ∧
      ∀ T : Over (Spec (CommRingCat.of F)),
        (upperUnipotent b c).carrier T = (upperRootPoints b c T).range ∧
        (lowerUnipotent b c).carrier T = (lowerRootPoints b c T).range

end Langlands.GroupScheme.QuasiSplitUnitary
