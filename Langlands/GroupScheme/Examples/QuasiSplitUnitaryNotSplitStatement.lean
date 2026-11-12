import Langlands.GroupScheme.Examples.QuasiSplitUnitary
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal

/-! # The quasi-split unitary group `U(1,1)` has no split maximal torus: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- For a nontrivial conjugation `c` of the quadratic extension `E/F`, the quasi-split unitary
group `U(1,1)` over `F` has no maximal torus that is split over `F`. -/
def NotSplitStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      ¬ HasSplitMaximalTorus (groupScheme b c)

end Langlands.GroupScheme.QuasiSplitUnitary
