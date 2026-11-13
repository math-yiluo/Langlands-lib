import Langlands.Representation.CuspidalSupport.RefinedJacquetLengthStatement
import Langlands.AllField.Representation.Geometric.RefinementFunctors
/-! Finite-length detection by proper refined Jacquet modules of a product Levi. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding RefinedJacquetFiniteLengthDetectionStatement
open Langlands.AllField.CuspidalSupport

/-- Internal product-Levi length criterion motivated by BZ77 §2.14(2).
If every quasicuspidal smooth subquotient vanishes and every proper refined
Jacquet module has finite length, then the original smooth representation
has finite length. This defines the proposition without proving it. -/
def RefinedJacquetFiniteLengthDetectionStatement.{uF, uV} : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
      (∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
        SmoothRep.IsSubquotient D A →
          IsLeviQuasicuspidal B D.representation → Subsingleton D) →
      (∀ S : Geometric.BlockRefinement B,
        Geometric.refinedParabolic F B S ≠ ⊤ →
          IsFiniteLength (MonoidAlgebra ℂ (Geometric.refinedLevi F B S))
            (T.normalizedRefinedJacquet B S A.representation).asModule) →
      IsFiniteLength (MonoidAlgebra ℂ (B.Levi F)) A.representation.asModule

end Langlands.AllField.CuspidalSupport
