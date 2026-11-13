import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Supplied integral root models and their actual residue roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

/-- Structural data for one generic root whose integral model maps to an actual
root subgroup of the specified neutral model's specified residue quotient.
The data do not assert existence for any building point or filtration. -/
structure IntegralRootSpecializationData
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (a : characterLattice S) where
  genericGroup : GroupScheme (Spec (CommRingCat.of K))
  genericInclusion : genericGroup ⟶ G
  representsGenericRoot : (RelativeRoot.subgroup i a).IsRepresentedBy genericInclusion
  model : IntegralModel R K genericGroup
  model_smooth : model.IsSmooth
  toNeutral : model.Hom D.neutral genericInclusion
  residueGroup : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  [residue_affine : IsAffineHom residueGroup.X.hom]
  residueProjection : model.specialFibre ⟶ residueGroup
  residueInclusion : residueGroup ⟶ Q.quotient
  residue_comm :
    residueProjection ≫ residueInclusion = toNeutral.specialFibreMap ≫ Q.projection
  residue_root : T.characterSpecialization hT a ∈
    relativeRoots (T.specialFibreInclusion ≫ Q.projection)
  representsResidueRoot :
    (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT a)).IsRepresentedBy residueInclusion
  kernel : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  [kernel_smooth : Smooth kernel.X.hom]
  kernelInclusion : kernel ⟶ model.specialFibre
  kernel_closed : IsClosedSubgroup kernelInclusion
  kernel_split : RelativeRoot.IsSplitUnipotent kernel
  isQuotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range kernelInclusion) residueProjection

attribute [instance] IntegralRootSpecializationData.residue_affine
  IntegralRootSpecializationData.kernel_smooth

namespace IntegralRootSpecializationData

variable {T : IntegralTorusData D S i} {hT : IsSplitTorus T.torus.toGrp}
  {Q : SpecialFibreQuotientData D} {a : characterLattice S}
  (A : IntegralRootSpecializationData T hT Q a)

/-- A stronger, separate obligation: the actual integral model represents the
all-test integral root functor. Generic representation and integral-point
identification alone do not establish this property. -/
def RepresentsIntegralRoot : Prop :=
  (RelativeRoot.subgroup T.inclusion ((T.genericCharacterEquiv hT).symm a)).IsRepresentedBy
    A.toNeutral.hom

/-- The residue-root map on a reduced section is the actual reduction in the
neutral model followed by the specified quotient projection. -/
theorem reduction_comm (x : A.model.integralSections) :
    rationalPoints.map A.residueInclusion
        (rationalPoints.map A.residueProjection (A.model.reduction x)) =
      rationalPoints.map Q.projection
        (D.neutral.reduction (rationalPoints.map A.toNeutral.hom x)) := by
  rw [A.toNeutral.reduction_naturality]
  change (A.model.reduction x ≫ A.residueProjection.hom.hom) ≫
      A.residueInclusion.hom.hom =
    (A.model.reduction x ≫ A.toNeutral.specialFibreMap.hom.hom) ≫ Q.projection.hom.hom
  simp only [Category.assoc]
  change A.model.reduction x ≫
      (A.residueProjection ≫ A.residueInclusion).hom.hom =
    A.model.reduction x ≫ (A.toNeutral.specialFibreMap ≫ Q.projection).hom.hom
  rw [A.residue_comm]

end IntegralRootSpecializationData
end Langlands.BruhatTits.IntegralModels
