import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # The integral facet torus in the reductive quotient -/

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

namespace IntegralTorusData

variable (T : IntegralTorusData D S i) (Q : SpecialFibreQuotientData D)

private instance neutralSpecialFibre_affine :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

/-- A closed split integral torus maps as a closed subgroup into any supplied
maximal reductive quotient of the neutral special fibre. -/
theorem isClosedSubgroup_quotientTorus
    (hT : T.IsClosedSplit) (hQ : Q.IsReductiveQuotient) :
    IsClosedSubgroup (T.specialFibreInclusion ≫ Q.projection) := by
  let : IsAffineHom Q.radical.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed _ _ Q.radicalInclusion
      hQ.1.isClosedSubgroup
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hspecial : IsSplitTorus T.specialFibre.toGrp :=
    IsSplitTorus.baseChange (IntegralModel.residueBaseMap R) hT.1
  exact hQ.1.isUnipotent.closed_torus_quotient unipotentClosedSubgroup
    hspecial.isTorus Q.radicalInclusion T.specialFibreInclusion
    (hT.2.baseChange (IntegralModel.residueBaseMap R))
    Q.projection hQ.2.1.2.2.2.le

variable [IsAffineHom T.torus.toGrp.X.hom]

private instance specialFibre_affine :
    IsAffineHom T.specialFibre.toGrp.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd T.torus.toGrp.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

/-- The actual special torus is isomorphic to its schematic image in the
specified reductive quotient. -/
def quotientTorusImageIso
    (hT : T.IsClosedSplit) (hQ : Q.IsReductiveQuotient) :
    T.specialFibre.toGrp ≅
      SchematicImage.image (T.specialFibreInclusion ≫ Q.projection) := by
  letI : IsAffineHom Q.radical.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed _ _ Q.radicalInclusion
      hQ.1.isClosedSubgroup
  letI : Smooth Q.radical.X.hom := hQ.1.smooth
  letI : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hspecial : IsSplitTorus T.specialFibre.toGrp :=
    IsSplitTorus.baseChange (IntegralModel.residueBaseMap R) hT.1
  exact hQ.1.isUnipotent.torusQuotientImageIso unipotentClosedSubgroup
    hspecial.isTorus Q.radicalInclusion T.specialFibreInclusion
    (hT.2.baseChange (IntegralModel.residueBaseMap R))
    Q.projection hQ.2.1.2.2.2.le

@[simp]
theorem quotientTorusImageIso_hom
    (hT : T.IsClosedSplit) (hQ : Q.IsReductiveQuotient) :
    (T.quotientTorusImageIso Q hT hQ).hom =
      SchematicImage.projection (T.specialFibreInclusion ≫ Q.projection) :=
  rfl

/-- Factoring the quotient-torus map through its schematic image uses the
constructed source-to-image isomorphism. -/
theorem quotientTorusImageIso_hom_inclusion
    (hT : T.IsClosedSplit) (hQ : Q.IsReductiveQuotient) :
    (T.quotientTorusImageIso Q hT hQ).hom ≫
        SchematicImage.inclusion (T.specialFibreInclusion ≫ Q.projection) =
      T.specialFibreInclusion ≫ Q.projection :=
  SchematicImage.projection_inclusion _

end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
