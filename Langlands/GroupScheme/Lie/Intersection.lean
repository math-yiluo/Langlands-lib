import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Actual Lie kernels of scheme-theoretic subgroup intersections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Lie

variable {R : CommRingCat.{u}} {P Q G : GroupScheme (Spec R)}
  (j : P ⟶ G) (j' : Q ⟶ G) (A : Type u) [CommRing A] [Algebra R A]

/-- Compatible actual tangent points lift to the scheme-theoretic intersection.
No smoothness, affineness or monomorphism hypothesis is needed. -/
def kernelIntersectionLift (x : lieKernel P A) (y : lieKernel Q A)
    (h : x.val ≫ j.hom.hom = y.val ≫ j'.hom.hom) :
    lieKernel (subgroupIntersection j j') A :=
  ⟨(subgroupIntersection_isPullback j j').lift x.val y.val h, by
    change reduction (subgroupIntersection j j') _ = 1
    apply (subgroupIntersection_isPullback j j').hom_ext
    · rw [← reduction_comp_hom, (subgroupIntersection_isPullback j j').lift_fst,
        x.property, MonObj.one_comp]
    · rw [← reduction_comp_hom, (subgroupIntersection_isPullback j j').lift_snd,
        y.property, MonObj.one_comp]⟩

@[simp] theorem kernelIntersectionLift_fst (x : lieKernel P A) (y : lieKernel Q A)
    (h : x.val ≫ j.hom.hom = y.val ≫ j'.hom.hom) :
    targetMap (subgroupIntersectionFst j j') A (kernelIntersectionLift j j' A x y h) =
      x := by
  apply Subtype.ext
  exact (subgroupIntersection_isPullback j j').lift_fst x.val y.val h

@[simp] theorem kernelIntersectionLift_snd (x : lieKernel P A) (y : lieKernel Q A)
    (h : x.val ≫ j.hom.hom = y.val ≫ j'.hom.hom) :
    targetMap (subgroupIntersectionSnd j j') A (kernelIntersectionLift j j' A x y h) =
      y := by
  apply Subtype.ext
  exact (subgroupIntersection_isPullback j j').lift_snd x.val y.val h

/-- The compatible lift is the unique actual tangent point with the given projections. -/
theorem kernelIntersectionLift_unique (x : lieKernel P A) (y : lieKernel Q A)
    (h : x.val ≫ j.hom.hom = y.val ≫ j'.hom.hom)
    (z : lieKernel (subgroupIntersection j j') A)
    (hz : targetMap (subgroupIntersectionFst j j') A z = x)
    (hz' : targetMap (subgroupIntersectionSnd j j') A z = y) :
    z = kernelIntersectionLift j j' A x y h := by
  apply Subtype.ext
  apply (subgroupIntersection_isPullback j j').hom_ext
  · exact (congrArg Subtype.val hz).trans
      ((subgroupIntersection_isPullback j j').lift_fst x.val y.val h).symm
  · exact (congrArg Subtype.val hz').trans
      ((subgroupIntersection_isPullback j j').lift_snd x.val y.val h).symm

/-- An actual ambient tangent vector is in the Lie-image of an intersection
exactly when the same vector is in both Lie-images. -/
theorem lieImage_subgroupIntersection_iff (x : lieKernel G A) :
    (∃ z : lieKernel (subgroupIntersection j j') A,
      z.val ≫ (subgroupIntersectionHom j j').hom.hom = x.val) ↔
    (∃ y : lieKernel P A, y.val ≫ j.hom.hom = x.val) ∧
      (∃ y : lieKernel Q A, y.val ≫ j'.hom.hom = x.val) := by
  constructor
  · rintro ⟨z, hz⟩
    constructor
    · refine ⟨targetMap (subgroupIntersectionFst j j') A z, ?_⟩
      change (z.val ≫ (subgroupIntersectionFst j j').hom.hom) ≫ j.hom.hom = _
      rw [Category.assoc]
      exact hz
    · refine ⟨targetMap (subgroupIntersectionSnd j j') A z, ?_⟩
      change (z.val ≫ (subgroupIntersectionSnd j j').hom.hom) ≫ j'.hom.hom = _
      rw [Category.assoc, ← (subgroupIntersection_isPullback j j').w]
      exact hz
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    let h := hy.trans hz.symm
    refine ⟨kernelIntersectionLift j j' A y z h, ?_⟩
    change ((subgroupIntersection_isPullback j j').lift y.val z.val h ≫
      (subgroupIntersectionFst j j').hom.hom) ≫ j.hom.hom = _
    rw [(subgroupIntersection_isPullback j j').lift_fst]
    exact hy

end Lie

end Langlands.GroupScheme
