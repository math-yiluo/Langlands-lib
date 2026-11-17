import Langlands.GroupScheme.FppfQuotientComparison

/-! # Comparing a subgroup with an extension through their common quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FppfExtensionComparison

variable {S : Scheme.{u}} {N M H Q : GroupScheme S}
    (i : N ⟶ H) (a : N ⟶ M) (j : M ⟶ H) (q : H ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (ha : a ≫ j = i)

include hq ha

/-- If a subgroup contains the kernel, a point of the ambient group with the
same quotient image as a point of the subgroup also lies in the subgroup. -/
theorem factors_of_equal_quotient_images {X : Over S}
    (x : X ⟶ H.X) (y : X ⟶ M.X)
    (hxy : x ≫ q.hom.hom = y ≫ (j ≫ q).hom.hom) :
    ∃ z : X ⟶ M.X, z ≫ j.hom.hom = x := by
  have hk : (x / (y ≫ j.hom.hom)) ≫ q.hom.hom = 1 := by
    rw [GrpObj.div_comp, hxy, Grp.comp_hom_hom, ← Category.assoc, div_self']
  have hi : x / (y ≫ j.hom.hom) ∈ (SubgroupFunctor.range i).carrier X := by
    rw [← hq.2.2.2, mem_range_kernelι_iff]
    exact hk
  obtain ⟨k, hk⟩ := SubgroupFunctor.mem_range.mp hi
  refine ⟨(k ≫ a.hom.hom) * y, ?_⟩
  rw [MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, ha, hk, div_mul_cancel]

/-- A monomorphism containing the full kernel of an fppf quotient is an
isomorphism if its composite to that quotient is fpqc. -/
def isoOfMonoContainingKernel [Mono j.hom.hom]
    [Flat (j ≫ q).hom.hom.left] [Surjective (j ≫ q).hom.hom.left]
    [QuasiCompact (j ≫ q).hom.hom.left] : M ≅ H := by
  classical
  let u := (j ≫ q).hom.hom.left
  let v := q.hom.hom.left
  let P := pullback u v
  let p : P ⟶ H.X.left := pullback.snd u v
  let X : Over S := Over.mk (p ≫ H.X.hom)
  let x : X ⟶ H.X := Over.homMk p
  let y : X ⟶ M.X := Over.homMk (pullback.fst u v) (by
    rw [← Over.w (j ≫ q).hom.hom, ← Category.assoc, pullback.condition,
      Category.assoc, Over.w q.hom.hom]
    rfl)
  have hxy : x ≫ q.hom.hom = y ≫ (j ≫ q).hom.hom :=
    Over.OverMorphism.ext (pullback.condition (f := u) (g := v)).symm
  let z := Classical.choose (factors_of_equal_quotient_images i a j q hq ha x y hxy)
  have hz : z ≫ j.hom.hom = x :=
    Classical.choose_spec (factors_of_equal_quotient_images i a j q hq ha x y hxy)
  have hz' : z.left ≫ j.hom.hom.left = p := congrArg (fun f => f.left) hz
  have : Flat p := by dsimp [p]; infer_instance
  have : Surjective p := by dsimp [p]; infer_instance
  have : QuasiCompact p := by dsimp [p]; infer_instance
  have hdesc : ∀ {Z : Scheme.{u}} (g h : Z ⟶ P),
      g ≫ p = h ≫ p → g ≫ z.left = h ≫ z.left := by
    intro Z g h hgh
    apply (cancel_mono j.hom.hom.left).mp
    simpa only [Category.assoc, hz'] using hgh
  let r := EffectiveEpi.desc p z.left hdesc
  have hr : r ≫ j.hom.hom.left = 𝟙 H.X.left := by
    apply (cancel_epi p).mp
    dsimp only [r]
    rw [← Category.assoc, EffectiveEpi.fac, hz', Category.comp_id]
  have hj : j.hom.hom.left ≫ r = 𝟙 M.X.left := by
    apply (cancel_mono j.hom.hom.left).mp
    rw [Category.assoc, hr, Category.comp_id, Category.id_comp]
  let e : M.X ≅ H.X :=
    Over.isoMk ⟨j.hom.hom.left, r, hj, hr⟩ (Over.w j.hom.hom)
  have : IsMonHom e.hom := by
    change IsMonHom j.hom.hom
    infer_instance
  exact Grp.mkIso' e

/-- The comparison's forward homomorphism is the original subgroup inclusion. -/
@[simp]
theorem isoOfMonoContainingKernel_hom [Mono j.hom.hom]
    [Flat (j ≫ q).hom.hom.left] [Surjective (j ≫ q).hom.hom.left]
    [QuasiCompact (j ≫ q).hom.hom.left] :
    (isoOfMonoContainingKernel i a j q hq ha).hom = j := rfl

end Langlands.GroupScheme.FppfExtensionComparison
