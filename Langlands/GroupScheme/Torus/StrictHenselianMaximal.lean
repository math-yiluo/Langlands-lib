import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.Torus.RelativeLiftingProof
import Langlands.CommutativeAlgebra.HenselianSections

/-! # Split maximal tori over strictly Henselian local rings -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- A reductive group over a strictly Henselian local ring contains an actual
closed split torus whose inclusion is maximal on every residue-field fibre. -/
theorem strictHenselianSplitMaximalTorus : StrictHenselianSplitMaximalTorusStatement.{u} :=
  strictHenselianSplitMaximalTorusReduction relativeSplitTorusLifting
    Langlands.CommutativeAlgebra.HenselianSections.henselianEtaleSection

end Langlands.GroupScheme
