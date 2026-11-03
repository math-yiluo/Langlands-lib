import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement

/-! # Reduction of root-annihilator centrality to dynamic geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SubgroupFunctor

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {F : SubgroupFunctor G} {j : H ⟶ G}
  {A : Type u} [CommRing A] [Algebra R A]

/-- A represented-subgroup lift of a dual-number identity-kernel point also
lies in the identity kernel: reduction and cancellation force this. -/
theorem IsRepresentedBy.exists_lieKernel_lift (hj : F.IsRepresentedBy j)
    (X : lieKernel G A) (hX : X.val ∈ F.carrier _) :
    ∃ Y : lieKernel H A, Y.val ≫ j.hom.hom = X.val := by
  have : Mono j.hom.hom := hj.1
  rw [← hj.2, mem_range] at hX
  obtain ⟨y, hy⟩ := hX
  refine ⟨⟨y, ?_⟩, hy⟩
  change Lie.reduction H y = 1
  apply (cancel_mono j.hom.hom).mp
  calc
    Lie.reduction H y ≫ j.hom.hom = Lie.reduction G (y ≫ j.hom.hom) := by
      simp only [Lie.reduction, Lie.affineMap_apply, Category.assoc]
    _ = Lie.reduction G X.val := congrArg (Lie.reduction G) hy
    _ = 1 := X.property
    _ = (1 : Lie.AffinePoints H A) ≫ j.hom.hom := (MonObj.one_comp _).symm

/-- The unique lift of an ambient Lie vector through a represented subgroup
containing its actual dual-number point. -/
def IsRepresentedBy.lieKernelLift (hj : F.IsRepresentedBy j)
    (X : lieKernel G A) (hX : X.val ∈ F.carrier _) : lieKernel H A :=
  (hj.exists_lieKernel_lift X hX).choose

@[simp] theorem IsRepresentedBy.lieKernelLift_comp (hj : F.IsRepresentedBy j)
    (X : lieKernel G A) (hX : X.val ∈ F.carrier _) :
    (hj.lieKernelLift X hX).val ≫ j.hom.hom = X.val :=
  (hj.exists_lieKernel_lift X hX).choose_spec

theorem IsRepresentedBy.lieKernelLift_unique (hj : F.IsRepresentedBy j)
    (X : lieKernel G A) (hX : X.val ∈ F.carrier _)
    (Y : lieKernel H A) (hY : Y.val ≫ j.hom.hom = X.val) :
    Y = hj.lieKernelLift X hX := by
  have : Mono j.hom.hom := hj.1
  apply Subtype.ext
  exact (cancel_mono j.hom.hom).mp (hY.trans (hj.lieKernelLift_comp X hX).symm)

end SubgroupFunctor

/-- The centralizer tangent description, its smoothness, and equality of
smooth closed full-Lie subgroups imply the actual centrality criterion. -/
theorem rootAnnihilatorCentrality_of_dynamic_geometry
    (hLie : DynamicLieStatement.{u}) (hSmooth : DynamicSmoothStatement.{u})
    (hEquality : LieSubgroupEqualityStatement.{u}) :
    RootAnnihilatorCentralityStatement.{u} := by
  intro k _ G _ _ _ T hT i ν hν
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hzero : weightSpace χ 0 = ⊤ :=
    weightSpace_zero_eq_top_of_annihilates_relativeRoots hT i ν hν
  let H := Dynamic.Affine.centralizerScheme χ
  let j : H ⟶ G := Dynamic.Affine.centralizerHom χ
  have hj : (Dynamic.centralizer χ).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have : Smooth H.X.hom := (hSmooth k G χ H j).2.1 hj
  have hfull : SubgroupFunctor.range j = ⊤ := by
    apply hEquality k G H j (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
    intro X
    apply hj.exists_lieKernel_lift X
    apply (hLie k G χ X).1.mpr
    change Additive.ofMul X ∈ weightSpace χ 0
    rw [hzero]
    exact Submodule.mem_top
  apply (isCentral_iff_dynamicCentralizer_eq_top χ).mpr
  exact hj.2.symm.trans hfull

end Langlands.GroupScheme
