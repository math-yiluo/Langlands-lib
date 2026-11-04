import Langlands.GroupScheme.Torus.CentralMaximalQuotientReduction
import Langlands.GroupScheme.Torus.CentralExtensionProof
import Langlands.GroupScheme.Torus.ImageProof

/-! # The quotient by a central maximal torus contains no torus -/

universe u

namespace Langlands.GroupScheme

/-- The fppf quotient of a smooth affine group by a central maximal torus receives only
trivial homomorphisms from tori, over every field and at every universe. -/
theorem centralMaximalTorusQuotientStatement : CentralMaximalTorusQuotientStatement.{u} :=
  centralMaximalTorusQuotientReduction.{u}
    centralTorusExtensionStatement.{u} torusImageClosedTorusStatement.{u}

end Langlands.GroupScheme
