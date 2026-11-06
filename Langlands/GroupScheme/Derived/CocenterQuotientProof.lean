import Langlands.GroupScheme.Derived.CocenterQuotientStructuralReduction
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityProof
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionProof

/-! # Existence of the cocenter quotient and its cocharacter properties -/

universe u

namespace Langlands.GroupScheme

/-- The cocenter of a connected reductive group over any field is an affine
commutative quotient torus, split over every extension splitting a supplied
maximal torus, with surjective integral cocharacter map from that torus. -/
theorem cocenterQuotientExistence :
    CocenterQuotientExistenceStatement.{u} :=
  cocenterQuotientExistence_of_product_of_torus_intersections
    derivedMaximalTorusProductSurjectivity derivedMaximalTorusIntersection

end Langlands.GroupScheme
