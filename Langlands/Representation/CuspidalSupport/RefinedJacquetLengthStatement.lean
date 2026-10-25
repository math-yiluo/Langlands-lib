import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Category.Subquotients
import Mathlib.RingTheory.FiniteLength

/-! Finite-length detection by proper refined Jacquet modules of a product Levi. -/

namespace Langlands.CuspidalSupport

/-- Internal product-Levi length criterion motivated by BZ77 §2.14(2).
If every quasicuspidal smooth subquotient vanishes and every proper refined
Jacquet module has finite length, then the original smooth representation
has finite length. This defines the proposition without proving it. -/
def RefinedJacquetFiniteLengthDetectionStatement.{uF, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      (∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
        SmoothRep.IsSubquotient D A →
          IsLeviQuasicuspidal B D.representation → Subsingleton D) →
      (∀ S : Geometric.BlockRefinement B,
        Geometric.refinedParabolic F.Carrier B S ≠ ⊤ →
          IsFiniteLength (MonoidAlgebra ℂ (Geometric.refinedLevi F.Carrier B S))
            (T.normalizedRefinedJacquet B S A.representation).asModule) →
      IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) A.representation.asModule

end Langlands.CuspidalSupport
