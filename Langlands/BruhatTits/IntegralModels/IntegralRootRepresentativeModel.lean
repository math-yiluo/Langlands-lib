import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration
import Langlands.GroupScheme.IntegralModel.SemilinearExtension

/-! # Integral models for supplied representatives of split-torus roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    {N : IntegralModel R K G} (A : IntegralSplitTorusData N i)
    [Smooth N.group.X.hom]

include A in
/-- Any supplied representative of the generic root has a smooth integral model
with geometrically connected fibres and a closed map into the ambient model. -/
theorem exists_model_of_rootRepresentative (a : characterLattice S) (ha : a ≠ 0)
    (U : GroupScheme (Spec (CommRingCat.of K))) (q : U ⟶ G)
    (hq : (RelativeRoot.subgroup i a).IsRepresentedBy q) :
    ∃ M : IntegralModel R K U, M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
      ∃ φ : M.Hom N q, IsClosedSubgroup φ.hom := by
  let e : A.rootGroup a ha ≅ U :=
    (A.rootInclusion_isRootSubgroup a ha).isoOfIsRepresentedBy hq
  have he : e.hom ≫ q = A.rootInclusion a ha :=
    (A.rootInclusion_isRootSubgroup a ha).isoOfIsRepresentedBy_hom_comp hq
  let M := (A.rootModel a ha).retarget e
  let φ : M.Hom N q :=
    { hom := (A.rootModelMap a ha).hom
      generic_comm := by
        change _ = ((A.rootModel a ha).genericIso.hom ≫ e.hom) ≫ q
        rw [Category.assoc, he]
        exact (A.rootModelMap a ha).generic_comm }
  refine ⟨M, ?_, ?_, φ, A.rootModelMap_isClosedSubgroup a ha⟩
  · exact IntegralModel.SplitRoot.model_isSmooth N A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero ha)
  · exact IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres
      N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero ha)

end Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData
