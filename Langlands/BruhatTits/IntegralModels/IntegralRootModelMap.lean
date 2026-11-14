import Langlands.BruhatTits.IntegralModels.CommonTorusMaximality
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootData
import Langlands.BruhatTits.IntegralModels.IntegralRootReductiveQuotient
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRootModels

/-! # Canonical maps between the actual integral root models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData source S i) (hT : IsSplitTorus T.torus.toGrp)

private instance sourceNeutral_smooth : Smooth source.neutral.group.X.hom :=
  source.neutral_smooth

private instance targetNeutral_smooth : Smooth target.neutral.group.X.hom :=
  target.neutral_smooth

/-- The canonical map between the full integral root representatives for the
source torus and its actual image torus. No smoothness of `φ` is required. -/
def integralRootMap (a : characterLattice S) (ha : a ≠ 0) :
    ((T.toIntegralSplitTorusData hT).rootModel a ha).group ⟶
      (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModel a ha).group :=
  RelativeRoot.SmoothQuotient.rootMap T.inclusion φ.neutral.hom
    ((T.toIntegralSplitTorusData hT).integralCharacter a)
    ((T.toIntegralSplitTorusData hT).rootModelMap a ha).hom
    (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap a ha).hom
    ((T.toIntegralSplitTorusData hT).rootModelMap_isRepresentedBy a ha)
    (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap_isRepresentedBy a ha)

/-- The integral root map factors the original composite into the target model. -/
theorem integralRootMap_comp (a : characterLattice S) (ha : a ≠ 0) :
    φ.integralRootMap T hT a ha ≫
        (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap a ha).hom =
      ((T.toIntegralSplitTorusData hT).rootModelMap a ha).hom ≫ φ.neutral.hom :=
  RelativeRoot.SmoothQuotient.rootMap_comp _ _ _ _ _ _ _

variable [IsLocalRing R]

/-- The transported torus has the actual composite residue inclusion. -/
theorem mapIntegralTorus_specialFibreInclusion :
    (φ.mapIntegralTorus T).specialFibreInclusion =
      T.specialFibreInclusion ≫ φ.neutralSpecialFibreMap :=
  (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map_comp _ _

/-- Transport along the model map preserves the exact facet character
specialization, including the supplied generic identification. -/
theorem mapIntegralTorus_characterSpecialization :
    (φ.mapIntegralTorus T).characterSpecialization hT =
      T.characterSpecialization hT := rfl

/-- The actual residue base change of the integral root map. -/
def residueRootMap (a : characterLattice S) (ha : a ≠ 0) :
    ((T.toIntegralSplitTorusData hT).rootModel a ha).specialFibre ⟶
      (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModel a ha).specialFibre :=
  (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
    (φ.integralRootMap T hT a ha)

/-- The original source-root composite factors through the actual target
root special fibre, as a map of schemes on every test. -/
theorem residueRootMap_comp (a : characterLattice S) (ha : a ≠ 0) :
    φ.residueRootMap T hT a ha ≫
        (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap =
      ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap ≫
        φ.neutralSpecialFibreMap := by
  unfold residueRootMap IntegralModel.Hom.specialFibreMap
  rw [← Functor.map_comp, φ.integralRootMap_comp T hT a ha, Functor.map_comp]
  rfl

/-- The special fibre of the integral root map is the canonical full
residue-root map induced by the actual neutral special-fibre morphism. -/
theorem residueRootMap_eq_rootMap (a : characterLattice S) (ha : a ≠ 0) :
    φ.residueRootMap T hT a ha =
      RelativeRoot.SmoothQuotient.rootMap T.specialFibreInclusion
        φ.neutralSpecialFibreMap (T.characterSpecialization hT a)
        ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap
        (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap
        ((T.toIntegralSplitTorusData hT).rootModelMap_specialFibre_isRepresentedBy a ha)
        (by
          rw [← φ.mapIntegralTorus_specialFibreInclusion T,
            ← φ.mapIntegralTorus_characterSpecialization T hT]
          exact ((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap_specialFibre_isRepresentedBy
            a ha) := by
  apply (((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootModelMap_specialFibre_isRepresentedBy
    a ha).hom_ext
  exact (φ.residueRootMap_comp T hT a ha).trans
    (RelativeRoot.SmoothQuotient.rootMap_comp _ _ _ _ _ _ _).symm

/-- The actual source-root map into the target reductive quotient factors
through the target root model's actual quotient map. -/
theorem residueRootMap_quotient_comp (Q : SpecialFibreQuotientData target)
    (a : characterLattice S) (ha : a ≠ 0) :
    φ.residueRootMap T hT a ha ≫
        ((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootReductiveQuotientMap Q a ha =
      ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap ≫
        φ.neutralSpecialFibreMap ≫ Q.projection := by
  rw [IntegralSplitTorusData.rootReductiveQuotientMap, ← Category.assoc,
    φ.residueRootMap_comp T hT a ha, Category.assoc]

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
