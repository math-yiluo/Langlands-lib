import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps
import Langlands.GroupScheme.CommutativeSubgroupIntersection
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.RetractionKernel
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Tori in the normal factor of an external semidirect product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

section Intersection

variable {B : Scheme.{u}} {S G : GroupScheme B} (a : AutomorphicAction S G)
    {M : CommGroupScheme B} (j : M.toGrp ⟶ a.semidirectProduct)

/-- The actual commutative intersection of a given commutative subgroup of
the semidirect product with its normal factor. -/
def semidirectTorusIntersection : CommGroupScheme B :=
  commutativeSubgroupIntersection j a.semidirectInl

/-- The inclusion of the intersection into the original normal factor. -/
abbrev semidirectTorusIntersectionInclusion :
    (a.semidirectTorusIntersection j).toGrp ⟶ G :=
  commutativeSubgroupIntersectionSnd j a.semidirectInl

/-- The inclusion of the intersection into the commutative source. -/
abbrev semidirectTorusIntersectionFst :
    (a.semidirectTorusIntersection j).toGrp ⟶ M.toGrp :=
  commutativeSubgroupIntersectionFst j a.semidirectInl

/-- The actual intersection square commutes. -/
theorem semidirectTorusIntersection_condition :
    a.semidirectTorusIntersectionFst j ≫ j =
      a.semidirectTorusIntersectionInclusion j ≫ a.semidirectInl :=
  commutativeSubgroupIntersection_condition j a.semidirectInl

/-- The projection kernel inside the commutative source is the same all-test
inverse image as the intersection with the normal factor. -/
theorem projectionKernel_isRepresentedBy :
    ((SubgroupFunctor.range a.semidirectInl).comap j).IsRepresentedBy
      (kernelι (j ≫ a.semidirectProjection)) := by
  refine ⟨inferInstance, ?_⟩
  apply SubgroupFunctor.ext
  intro V
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap,
    a.mem_range_semidirectInl_iff]
  simp only [Grp.comp_hom_hom, Category.assoc]

/-- The intersection is canonically the actual projection kernel. -/
def semidirectTorusIntersectionKernelIso [IsSeparated S.X.hom] :
    (a.semidirectTorusIntersection j).toGrp ≅
      kernel (j ≫ a.semidirectProjection) :=
  (SubgroupFunctor.IsRepresentedBy.comap_subgroupIntersectionFst
    (⟨inferInstance, rfl⟩ :
      (SubgroupFunctor.range a.semidirectInl).IsRepresentedBy a.semidirectInl)
    a.isClosedSubgroup_semidirectInl j).isoOfIsRepresentedBy
      (a.projectionKernel_isRepresentedBy j)

/-- A closed commutative source gives a closed intersection in the normal factor. -/
theorem isClosedSubgroup_semidirectTorusIntersectionInclusion
    (hj : IsClosedSubgroup j) :
    IsClosedSubgroup (a.semidirectTorusIntersectionInclusion j) :=
  isClosedSubgroup_commutativeSubgroupIntersectionSnd j a.semidirectInl hj

variable (f : S ⟶ M.toGrp) (hf : f ≫ j = a.semidirectInr)

include hf in
/-- Containment of the external factor makes its lift a group-scheme section
of the projection from the commutative source. -/
theorem semidirectTorusProjection_section :
    f ≫ (j ≫ a.semidirectProjection) = 𝟙 S := by
  rw [← Category.assoc, hf, a.semidirectInr_comp_projection]

include hf in
/-- Every point of the intersection is fixed by the original external action,
on every test scheme, because both points lift to the commutative source. -/
theorem semidirectTorusIntersection_fixed (V : Over B)
    (s : V ⟶ S.X) (x : V ⟶ (a.semidirectTorusIntersection j).X) :
    a.act s (x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom) =
      x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom := by
  apply (cancel_mono a.semidirectInl.hom.hom).mp
  rw [← a.semidirect_conjugation, conjugation_act]
  have hx :
      (x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom) ≫
        a.semidirectInl.hom.hom =
      (x ≫ (a.semidirectTorusIntersectionFst j).hom.hom) ≫ j.hom.hom := by
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
      ← a.semidirectTorusIntersection_condition j, Grp.comp_hom_hom]
  have hs : s ≫ a.semidirectInr.hom.hom = (s ≫ f.hom.hom) ≫ j.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
  have hcomm :
      (s ≫ a.semidirectInr.hom.hom) *
        ((x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom) ≫
          a.semidirectInl.hom.hom) =
      ((x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom) ≫
          a.semidirectInl.hom.hom) * (s ≫ a.semidirectInr.hom.hom) := by
    rw [hx, hs, ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

end Intersection

section Field

variable {k : Type u} [Field k]
    {S G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom S.X.hom] [IsAffineHom G.X.hom]
    (a : AutomorphicAction S G) {M : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : M.toGrp ⟶ a.semidirectProduct) (hj : IsClosedSubgroup j)
    (f : S ⟶ M.toGrp) (hf : f ≫ j = a.semidirectInr)

omit [IsAffineHom S.X.hom] in
include hj in
/-- The actual intersection is affine as a closed subgroup of the normal factor. -/
theorem semidirectTorusIntersection_isAffineHom :
    IsAffineHom (a.semidirectTorusIntersection j).X.hom := by
  let i := a.semidirectTorusIntersectionInclusion j
  let : IsClosedImmersion i.hom.hom.left :=
    a.isClosedSubgroup_semidirectTorusIntersectionInclusion j hj
  rw [← i.hom.hom.w]
  infer_instance

include hj hf in
/-- A torus in the semidirect product containing the external factor has a
torus as its scheme-theoretic intersection with the normal factor. -/
theorem isTorus_semidirectTorusIntersection (hM : IsTorus M.toGrp) :
    IsTorus (a.semidirectTorusIntersection j).toGrp := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom M.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let q := j ≫ a.semidirectProjection
  let : IsAffineHom (kernel q).X.hom := by
    rw [← (kernelι q).hom.hom.w]
    infer_instance
  exact IsTorus.of_iso (a.semidirectTorusIntersectionKernelIso j)
    (Torus.isTorus_kernel_of_section q f
      (a.semidirectTorusProjection_section j f hf) hM)

end Field

section MaximalExtension

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (a : AutomorphicAction S.toGrp G)

/-- A split external torus lies in a maximal torus of the actual semidirect
product. Its actual intersection with the normal factor is a closed affine
torus fixed pointwise by the external action. -/
theorem exists_maximalTorus_with_fixed_intersection
    (hS : IsSplitTorus S.toGrp) (hG : Smooth G.X.hom) :
    ∃ (M : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : M.toGrp ⟶ a.semidirectProduct) (f : S.toGrp ⟶ M.toGrp),
      IsMaximalTorus j ∧ f ≫ j = a.semidirectInr ∧
      IsTorus (a.semidirectTorusIntersection j).toGrp ∧
      IsClosedSubgroup (a.semidirectTorusIntersectionInclusion j) ∧
      IsAffineHom (a.semidirectTorusIntersection j).X.hom ∧
      Smooth (a.semidirectTorusIntersection j).X.hom ∧
      ConnectedSpace (a.semidirectTorusIntersection j).X.left ∧
      ∀ (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ S.X)
        (x : V ⟶ (a.semidirectTorusIntersection j).X),
        a.act s (x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom) =
          x ≫ (a.semidirectTorusIntersectionInclusion j).hom.hom := by
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : Smooth S.X.hom := hS.smooth
  let : Smooth G.X.hom := hG
  obtain ⟨M, j, hM, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType a.semidirectProduct
      a.semidirectInr hS.isTorus a.isClosedSubgroup_semidirectInr
  have hT := a.isTorus_semidirectTorusIntersection j hM.2.1 f hf hM.1
  exact ⟨M, j, f, hM, hf, hT,
    a.isClosedSubgroup_semidirectTorusIntersectionInclusion j hM.2.1,
    a.semidirectTorusIntersection_isAffineHom j hM.2.1,
    hT.smooth, hT.connectedSpace, a.semidirectTorusIntersection_fixed j f hf⟩

end MaximalExtension

end Langlands.GroupScheme.AutomorphicAction
