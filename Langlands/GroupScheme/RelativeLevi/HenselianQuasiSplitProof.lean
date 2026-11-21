import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementProof
import Langlands.GroupScheme.RelativeLevi.BorelSchemeProof
import Langlands.GroupScheme.RelativeLevi.HenselianFiniteEtaleSplitReduction

/-! # Reductive groups over henselian local rings with finite residue field -/

universe u

namespace Langlands.GroupScheme

/-- A reductive group over a henselian local ring with finite residue field
is quasi-split and splits over a finite étale local algebra. -/
theorem henselianFiniteResidueQuasiSplit : HenselianFiniteResidueQuasiSplitStatement.{u} :=
  henselianFiniteResidueQuasiSplit_of_inputs relativeBorelScheme.{u}
    Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement.{u}

end Langlands.GroupScheme
