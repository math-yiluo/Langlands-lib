import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction
import Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitProof

/-! # Quasi-splitness over Henselian discretely valued fields: the proof -/

universe u

namespace Langlands.GroupScheme

/-- Every connected reductive group over a Henselian discretely valued field with algebraically
closed residue field is quasi-split (Kaletha–Prasad 2023, Corollary 2.3.8). -/
theorem henselianDiscreteQuasiSplit : HenselianDiscreteQuasiSplitStatement.{u} :=
  henselianDiscreteQuasiSplit_of_dimensionLEOne dimensionLEOneQuasiSplit

end Langlands.GroupScheme
