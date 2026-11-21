import Langlands.GroupScheme.Rational.RealPointComponentsFixedCorootAssembly
import Langlands.GroupScheme.Rational.RealReductiveSplitTorusComponentsProof
import Langlands.GroupScheme.Rational.RealFixedSimpleCorootSign

/-! # Connected components of real points -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Real points are connected in the simply connected case and have finitely many
connected components in the connected reductive case. -/
theorem realPointComponents : RealPointComponentsStatement :=
  realPointComponents_of_fixedSimpleCorootSigns realReductiveSplitTorusComponents
    fun G _ hG =>
      letI : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
      RealPointTopology.fixedSimpleCorootSignsInIdentity_of_isConnectedReductive G
        hG.isSemisimple.isConnectedReductive

end Langlands.GroupScheme
