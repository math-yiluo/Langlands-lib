import Langlands.BruhatTits.IntegralModels.IntegralTorusRootData

/-! # Split integral-torus data for the full supplied model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D S i)

/-- The supplied integral split torus, mapped into the full model through its
neutral component, with the same specified generic torus identification. -/
def toFullIntegralSplitTorusData (hT : IsSplitTorus T.torus.toGrp) :
    IntegralSplitTorusData D.full i where
  torus := T.torus
  isSplit := hT
  inclusion := T.inclusion ≫ D.inclusion.hom
  genericIso := CommGroupScheme.isoOfGroupIso T.genericIso
  generic_comm := by
    change (baseChange (Spec.algebraMap R K)).map (T.inclusion ≫ D.inclusion.hom) ≫
        D.full.genericIso.hom = T.genericIso.hom ≫ i
    rw [Functor.map_comp, Category.assoc, D.inclusion.generic_comm,
      Category.comp_id]
    exact T.generic_comm

@[simp] theorem toFullIntegralSplitTorusData_inclusion
    (hT : IsSplitTorus T.torus.toGrp) :
    (T.toFullIntegralSplitTorusData hT).inclusion = T.inclusion ≫ D.inclusion.hom := rfl

/-- Passing to the full model preserves the integral character used for root models. -/
@[simp] theorem toFullIntegralSplitTorusData_integralCharacter
    (hT : IsSplitTorus T.torus.toGrp) (a : characterLattice S) :
    (T.toFullIntegralSplitTorusData hT).integralCharacter a =
      (T.toIntegralSplitTorusData hT).integralCharacter a := rfl

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
