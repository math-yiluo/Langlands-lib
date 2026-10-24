import Langlands.ClassField.Global.Cohomology
import Langlands.ClassField.Global.IdeleClassGaloisDescentStatement
import Langlands.ClassField.Global.IdeleClassNormGaloisProductStatement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Conditional comparison of cyclic idele-class H² with the norm index -/

namespace Langlands.ClassField.Global

universe u v

/-- Galois descent and compatibility of the actual idele-class norm with the
Galois product imply that the cardinality of cyclic relative H² divides the
norm index. This definition states the conditional comparison without proving it. -/
def CyclicH2NormIndexComparison : Prop :=
  IdeleClassGaloisDescent.{u, v} →
  IdeleClassNormGaloisProduct.{u, v} →
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    Nat.card (relativeIdeleClassCohomology F E 2 : Type v) ∣
      (Langlands.Global.AdelicFunctoriality.ideleClassNorm
        (K := F) (L := E)).toMonoidHom.range.index

end Langlands.ClassField.Global
