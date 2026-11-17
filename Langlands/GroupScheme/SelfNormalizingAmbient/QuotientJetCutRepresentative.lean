import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientJetEmbedding

/-! # Actual cut representatives of retained quotient jet ideals -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SelfNormalizingAmbient.ProperQuotientJetData

open AffineCoordinates Corepresented

private theorem closed_mono {X Y : Scheme} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) : Mono f := by
  let : IsClosedImmersion f := hf
  exact SurjectiveOnStalks.mono_of_injective f.isClosedEmbedding.injective

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  {i : H ⟶ G} {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i}
  (D : ProperQuotientJetData i Q)

/-- The actual group with coordinate algebra the retained quotient `B/I`. -/
def cutGroup : GroupScheme (Spec R) :=
  Corepresented.cutGroupScheme (Corepresented.isCutOutBy_range D.ideal_range)

/-- The actual quotient-coordinate inclusion into the fixed ambient group. -/
def cutInclusion : D.cutGroup ⟶ groupScheme (functor G) (corepresentation G) :=
  Corepresented.cutHom (Corepresented.isCutOutBy_range D.ideal_range)

/-- The underlying cut inclusion is the spectrum of the retained quotient map. -/
theorem cutInclusion_left :
    D.cutInclusion.hom.hom.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.ideal)) :=
  Corepresented.cutHom_left _

/-- The retained quotient algebra represents the original subgroup on every test. -/
theorem cutInclusion_range :
    SubgroupFunctor.range D.cutInclusion =
      SubgroupFunctor.range (coordinateHom i) := by
  rw [cutInclusion, Corepresented.range_cutHom]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro y
  exact (Corepresented.mem_range_iff_mem_affineSubgroups D.ideal_range y).symm

/-- The original actual closed subgroup is the retained quotient-coordinate group,
with its ambient inclusion preserved. -/
def cutRepresentativeIso (hi : IsClosedSubgroup i) : H ≅ D.cutGroup := by
  letI : IsClosedImmersion i.hom.hom.left := hi
  letI : IsClosedImmersion (coordinateHom i).hom.hom.left := by
    infer_instance
  letI : Mono (coordinateHom i).hom.hom.left := closed_mono _ inferInstance
  letI : Mono (coordinateHom i).hom.hom := Over.mono_of_mono_left _
  letI : IsClosedImmersion D.cutInclusion.hom.hom.left := by
    rw [cutInclusion_left]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : Mono D.cutInclusion.hom.hom.left := closed_mono _ inferInstance
  letI : Mono D.cutInclusion.hom.hom := Over.mono_of_mono_left _
  let hr : (SubgroupFunctor.range (coordinateHom i)).IsRepresentedBy (coordinateHom i) :=
    ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range (coordinateHom i)).IsRepresentedBy D.cutInclusion :=
    ⟨inferInstance, D.cutInclusion_range⟩
  exact hr.isoOfIsRepresentedBy hr'

@[reassoc]
theorem cutRepresentativeIso_hom_comp (hi : IsClosedSubgroup i) :
    (D.cutRepresentativeIso hi).hom ≫ D.cutInclusion = coordinateHom i := by
  unfold cutRepresentativeIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The actual group comparison gives the original quotient map on scheme functions. -/
theorem cutRepresentativeIso_hom_left (hi : IsClosedSubgroup i) :
    (D.cutRepresentativeIso hi).hom.hom.hom.left ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.ideal)) =
      i.hom.hom.left ≫ (groupSchemeIso G).inv.hom.hom.left := by
  have hh := congrArg
    (fun (f : H ⟶ groupScheme (functor G) (corepresentation G)) => f.hom.hom.left)
    (D.cutRepresentativeIso_hom_comp hi)
  change (D.cutRepresentativeIso hi).hom.hom.hom.left ≫ D.cutInclusion.hom.hom.left = _ at hh
  rw [D.cutInclusion_left] at hh
  exact hh

end Langlands.GroupScheme.SelfNormalizingAmbient.ProperQuotientJetData
