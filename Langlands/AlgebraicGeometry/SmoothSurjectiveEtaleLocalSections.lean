import Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSectionsStatement
import Langlands.AlgebraicGeometry.SmoothEtaleLocalSections

/-! # Etale local sections of smooth surjective scheme morphisms: proof (Stacks 055U) -/

universe u

namespace Langlands.AlgebraicGeometry

/-- **Stacks 055U.** Every smooth surjective morphism of schemes has a section after pullback
along a single surjective etale morphism of schemes. -/
theorem smoothSurjectiveEtaleLocalSections : SmoothSurjectiveEtaleLocalSectionsStatement.{u} :=
  fun _ _ f _ _ => hasEtaleLocalSections_of_smooth f

end Langlands.AlgebraicGeometry
