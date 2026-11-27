import Langlands.LinearAlgebra.GMFamilySmoothExtension
import Langlands.LinearAlgebra.GMFamiliesSplittingProof
import Langlands.LinearAlgebra.GMFamiliesDescentProof
import Langlands.LinearAlgebra.GMFamilyAlternateSplittingProof

/-! # Arthur's lemmas on `(G, M)`-families

The conjunction `GMFamilyStatement` of `Langlands.LinearAlgebra.GMFamiliesStatement`: Arthur 2005,
§17, Lemma 17.1 (smooth extension), Lemma 17.4 (splitting formula), Lemma 17.5 (descent formula,
for Levi subgroups over the same field) and Lemma 17.6 (alternate splitting formula). Each
component is the theorem proved in its own module. -/

universe u

namespace Langlands.GMFamily

/-- **Arthur 2005, Lemmas 17.1, 17.4, 17.5 (same field) and 17.6.** The four statements on
`(G, M)`-families hold at every universe `u`. -/
theorem gmFamily : GMFamilyStatement.{u} :=
  ⟨smoothExtension.{u}, splittingFormula.{u}, descentFormula.{u}, alternateSplittingFormula.{u}⟩

end Langlands.GMFamily
