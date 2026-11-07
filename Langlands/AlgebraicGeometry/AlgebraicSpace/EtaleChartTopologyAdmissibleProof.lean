import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyAdmissibleStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected

/-!
# Proof of Conrad's Proposition 5.4 (corrected to locally separated spaces)

The étale-chart topology is admissible, unique on quasi-separated, locally separated spaces
locally of finite type, and has the separated-space properties; hence it witnesses the
corrected Proposition 5.4.
-/

universe u

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

/-- Over a henselian valued field, the étale-chart topology has the six properties of the
corrected Proposition 5.4. -/
theorem etaleChartTopology_isAdmissible (hK : IsHenselianValuedField K) :
    IsAdmissibleRationalPointTopology K (etaleChartTopology K) :=
  ⟨fun _ _ f _ hY => continuous_ringPointsMap hK hY.1 f,
    fun U hU => isHomeomorph_schemeRingPointsEquiv hK U hU.1,
    fun _ _ _ _ p' p'' f' f'' hP hX' hX'' hX h =>
      isEmbedding_pullbackPoints hK p' p'' f' f'' hP.1 hX'.1 hX''.1 hX h,
    fun _ _ f hX' hX hf => isOpenEmbedding_ringPointsMap hK hX'.1 hX.1 f hf,
    fun _ _ f hX' hX hf => isClosedEmbedding_ringPointsMap hK hX'.1 hX.1 f hf,
    fun _ _ f hX' hX hf => isLocalHomeomorph_ringPointsMap hK hX'.1 hX f hf⟩

/-- The separated-space properties of the étale-chart topology. -/
theorem etaleChartTopology_separatedProperties (hK : IsHenselianValuedField K) :
    SeparatedRationalPointTopologyProperties K (etaleChartTopology K) := fun _ hX hs =>
  ⟨t2Space_etaleChartTopology hK hX hs,
    fun _ => totallyDisconnectedSpace_etaleChartTopology hK hX hs,
    fun _ => locallyCompactSpace_etaleChartTopology hK hX⟩

/-- **Conrad's Proposition 5.4, proof of existence and uniqueness** (corrected to locally
separated spaces). -/
theorem etaleChartTopologyAdmissible : EtaleChartTopologyAdmissibleStatement.{u} :=
  fun _ _ hK => ⟨etaleChartTopology_isAdmissible hK,
    fun τ' hτ' X hX => eq_etaleChartTopology_of_isAdmissible τ' hτ' X hX,
    etaleChartTopology_separatedProperties hK⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
