import Langlands.GroupScheme.SubgroupPreimageKernel
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Fppf quotients on actual subgroup preimages -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SubgroupPreimage

variable {S : Scheme.{u}} {G Q H K : GroupScheme S}
    (q : G ⟶ Q) (j : K ⟶ Q)

/-- Finite presentation of a quotient map is preserved on an actual subgroup preimage. -/
theorem locallyOfFinitePresentation_projection
    [LocallyOfFinitePresentation q.hom.hom.left] :
    LocallyOfFinitePresentation (projection q j).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance

/-- An actual subgroup preimage represents the inverse-image subgroup functor. -/
theorem isRepresentedBy_inclusion [Mono j.hom.hom] :
    ((SubgroupFunctor.range j).comap q).IsRepresentedBy (inclusion q j) :=
  ⟨(isPullback q j).flip.mono_snd_of_mono, range_inclusion q j⟩

section Represented

variable {P : GroupScheme S} {p : P ⟶ G} [Mono j.hom.hom]
    (hp : ((SubgroupFunctor.range j).comap q).IsRepresentedBy p)

/-- Any representative of the inverse-image subgroup is isomorphic to the
actual group-scheme preimage. -/
def representedIso : P ≅ groupScheme q j :=
  hp.isoOfIsRepresentedBy (isRepresentedBy_inclusion q j)

/-- The comparison identifies the representative's inclusion with the actual one. -/
@[reassoc]
theorem representedIso_hom_comp :
    (representedIso q j hp).hom ≫ inclusion q j = p :=
  hp.isoOfIsRepresentedBy_hom_comp (isRepresentedBy_inclusion q j)

/-- The quotient projection on an arbitrary representative of the inverse image. -/
def representedProjection : P ⟶ K :=
  (representedIso q j hp).hom ≫ projection q j

/-- The represented projection lifts the restriction of the original quotient. -/
@[reassoc]
theorem representedProjection_comp :
    representedProjection q j hp ≫ j = p ≫ q := by
  rw [representedProjection, Category.assoc, ← subgroupIntersection_condition,
    ← Category.assoc, representedIso_hom_comp]

/-- Flatness of the quotient survives on every representative of its inverse image. -/
theorem flat_representedProjection [Flat q.hom.hom.left] :
    Flat (representedProjection q j hp).hom.hom.left := by
  let e := representedIso q j hp
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  have : IsIso e.hom.hom.hom.left := (Over.forget S).map_isIso e.hom.hom.hom
  let : Flat (projection q j).hom.hom.left := flat_projection q j
  change Flat (e.hom.hom.hom.left ≫ (projection q j).hom.hom.left)
  infer_instance

/-- Surjectivity of the quotient survives on every representative of its inverse image. -/
theorem surjective_representedProjection [Surjective q.hom.hom.left] :
    Surjective (representedProjection q j hp).hom.hom.left := by
  let e := representedIso q j hp
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  have : IsIso e.hom.hom.hom.left := (Over.forget S).map_isIso e.hom.hom.hom
  let : Surjective (projection q j).hom.hom.left := surjective_projection q j
  change Surjective (e.hom.hom.hom.left ≫ (projection q j).hom.hom.left)
  infer_instance

/-- Local finite presentation survives on every representative of the inverse image. -/
theorem locallyOfFinitePresentation_representedProjection
    [LocallyOfFinitePresentation q.hom.hom.left] :
    LocallyOfFinitePresentation (representedProjection q j hp).hom.hom.left := by
  let e := representedIso q j hp
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  have : IsIso e.hom.hom.hom.left := (Over.forget S).map_isIso e.hom.hom.hom
  let : LocallyOfFinitePresentation (projection q j).hom.hom.left :=
    locallyOfFinitePresentation_projection q j
  change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ (projection q j).hom.hom.left)
  infer_instance

end Represented

/-- Flatness of the subgroup and of the quotient imply flatness of its preimage. -/
theorem flat [Flat q.hom.hom.left] [Flat K.X.hom] :
    Flat (groupScheme q j).X.hom := by
  let : Flat (projection q j).hom.hom.left := flat_projection q j
  rw [← Over.w (projection q j).hom.hom]
  infer_instance

/-- Local finite presentation of a quotient and subgroup imply local finite
presentation of their preimage over the base. -/
theorem locallyOfFinitePresentation [LocallyOfFinitePresentation q.hom.hom.left]
    [LocallyOfFinitePresentation K.X.hom] :
    LocallyOfFinitePresentation (groupScheme q j).X.hom := by
  let : LocallyOfFinitePresentation (projection q j).hom.hom.left :=
    locallyOfFinitePresentation_projection q j
  rw [← Over.w (projection q j).hom.hom]
  infer_instance

variable (h : H ⟶ G) [Mono h.hom.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q)

/-- The original presented kernel identifies with the full kernel of the
projection of any subgroup preimage. -/
def quotientKernelIso : H ≅ kernel (projection q j) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (SubgroupFunctor.range h).IsRepresentedBy h from ⟨inferInstance, rfl⟩)
    ⟨inferInstance, hq.2.2.2⟩ ≪≫ (kernelIso q j).symm

/-- The original kernel embedded in the actual subgroup preimage. -/
def quotientKernelInclusion : H ⟶ groupScheme q j :=
  (quotientKernelIso q j h hq).hom ≫ kernelι (projection q j)

instance quotientKernelInclusion_mono : Mono (quotientKernelInclusion q j h hq).hom.hom := by
  let e := quotientKernelIso q j h hq
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  change Mono (e.hom.hom.hom ≫ (kernelι (projection q j)).hom.hom)
  infer_instance

/-- The new kernel inclusion is compatible with the original inclusion into `G`. -/
@[reassoc]
theorem quotientKernelInclusion_comp :
    quotientKernelInclusion q j h hq ≫ inclusion q j = h := by
  let hh : (SubgroupFunctor.range h).IsRepresentedBy h := ⟨inferInstance, rfl⟩
  let hker : (SubgroupFunctor.range h).IsRepresentedBy (kernelι q) :=
    ⟨inferInstance, hq.2.2.2⟩
  have he : (hh.isoOfIsRepresentedBy hker).hom ≫ kernelι q = h :=
    hh.isoOfIsRepresentedBy_hom_comp hker
  have hk : (kernelIso q j).inv ≫ kernelι (projection q j) ≫ inclusion q j = kernelι q := by
    rw [← kernelIso_hom_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change ((hh.isoOfIsRepresentedBy hker).hom ≫ (kernelIso q j).inv ≫
    kernelι (projection q j)) ≫ inclusion q j = h
  simpa only [Category.assoc, hk] using he

/-- This inclusion represents precisely the full kernel of the new projection. -/
theorem range_quotientKernelInclusion :
    SubgroupFunctor.range (quotientKernelInclusion q j h hq) =
      SubgroupFunctor.range (kernelι (projection q j)) :=
  SubgroupFunctor.range_iso_comp (quotientKernelIso q j h hq) _

/-- The preimage projection is an fppf quotient by the original presented kernel. -/
theorem isFppfQuotient_projection_of_kernel :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (quotientKernelInclusion q j h hq))
      (projection q j) := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  exact ⟨flat_projection q j, surjective_projection q j,
    locallyOfFinitePresentation_projection q j, (range_quotientKernelInclusion q j h hq).symm⟩

/-- Closedness of the old kernel and of the subgroup imply closedness of the
kernel inclusion into the preimage. -/
theorem isClosedSubgroup_quotientKernelInclusion
    (hh : IsClosedSubgroup h) (hj : IsClosedSubgroup j) :
    IsClosedSubgroup (quotientKernelInclusion q j h hq) :=
  IsClosedSubgroup.of_comp (isClosedSubgroup q j hj)
    (by rw [quotientKernelInclusion_comp]; exact hh)

/-- A central original kernel remains central in the subgroup preimage. -/
theorem isCentral_quotientKernelInclusion [Mono j.hom.hom] (hh : IsCentral h) :
    IsCentral (quotientKernelInclusion q j h hq) := by
  let : Mono (inclusion q j).hom.hom := (isRepresentedBy_inclusion q j).1
  apply IsCentral.of_comp (by infer_instance) (j := inclusion q j)
  rw [quotientKernelInclusion_comp]
  exact hh

end SubgroupPreimage

end Langlands.GroupScheme
