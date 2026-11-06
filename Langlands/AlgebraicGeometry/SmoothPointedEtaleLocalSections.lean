import Langlands.AlgebraicGeometry.SmoothPointedEtaleLocalSectionsStatement
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction

/-! # Pointed etale local sections of smooth morphisms: exact proof -/

universe u

namespace Langlands.AlgebraicGeometry

/-- A prescribed residue-field point extends over a pointed etale neighbourhood. -/
theorem smoothPointedEtaleLocalSections : SmoothPointedEtaleLocalSectionsStatement.{u} := by
  intro X S f hf s x₀ hx₀
  let := hf
  exact exists_pointed_etale_section f s x₀ hx₀

end Langlands.AlgebraicGeometry
