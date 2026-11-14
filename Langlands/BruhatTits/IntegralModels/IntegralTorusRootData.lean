import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.BruhatTits.IntegralModels.IntegralRootSpecialFibre

/-! # Root-model data from the supplied integral torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i)

/-- Use the same integral torus, inclusion and generic identification as
compatible split-torus data for the actual neutral model. -/
def toIntegralSplitTorusData (hT : IsSplitTorus T.torus.toGrp) :
    IntegralSplitTorusData D.neutral i where
  torus := T.torus
  isSplit := hT
  inclusion := T.inclusion
  genericIso := CommGroupScheme.isoOfGroupIso T.genericIso
  generic_comm := T.generic_comm

@[simp] theorem toIntegralSplitTorusData_integralCharacter
    (hT : IsSplitTorus T.torus.toGrp) (a : characterLattice S) :
    (T.toIntegralSplitTorusData hT).integralCharacter a =
      (T.genericCharacterEquiv hT).symm a := rfl

variable [IsLocalRing R]

@[simp] theorem toIntegralSplitTorusData_specialFibreInclusion
    (hT : IsSplitTorus T.torus.toGrp) :
    (T.toIntegralSplitTorusData hT).specialFibreInclusion =
      T.specialFibreInclusion := rfl

/-- The root-model specialization is exactly the specialization already
used in the facet Lie-weight sign formula. -/
@[simp] theorem toIntegralSplitTorusData_characterSpecialization
    (hT : IsSplitTorus T.torus.toGrp) :
    (T.toIntegralSplitTorusData hT).characterSpecialization =
      T.characterSpecialization hT := rfl

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
