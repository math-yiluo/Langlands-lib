import Langlands.GroupScheme.Reductive.AlmostAllPlacesQuasiSplitHenselianReduction
import Langlands.GroupScheme.RelativeLevi.HenselianQuasiSplitProof

/-! # Quasi-splitness and torsor points at almost all finite places -/

universe u

namespace Langlands.GroupScheme

/-- A connected reductive group over a number field is quasi-split at almost all
finite completions, and each torsor under it has a point at almost all finite completions. -/
theorem almostAllPlacesQuasiSplit : AlmostAllPlacesQuasiSplitStatement.{u} :=
  almostAllPlacesQuasiSplit_of_henselian.{u} henselianFiniteResidueQuasiSplit.{u}

end Langlands.GroupScheme
