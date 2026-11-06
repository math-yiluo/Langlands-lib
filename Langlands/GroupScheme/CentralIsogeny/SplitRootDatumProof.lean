import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.CentralIsogeny.RootDatumHomConstruction

/-! # Central isogenies induce morphisms of the supplied root data -/

universe u

namespace Langlands.GroupScheme

/-- **Milne 23.5, central case.** Actual character pullback and cocharacter
pushforward give the required morphism of the supplied root data. -/
theorem centralIsogenyRootDatumHom : CentralIsogenyRootDatumHomStatement.{u} := by
  apply centralIsogenyRootDatumHom_of_kernel_containment
  intro k _ G G' hG _hG' T i _hT hi φ hφ
  rw [← maximalTorusCentralizer k G hG T i hi]
  exact hφ.kernel_range_le_center.trans (center_le_torusCentralizer i)

end Langlands.GroupScheme
