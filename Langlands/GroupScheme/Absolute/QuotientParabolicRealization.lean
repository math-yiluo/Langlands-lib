import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization

/-! # Parabolic realization by the reduced inverse image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientSubgroupRealization

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- The supplied target map is the surjective image of some parabolic subgroup of the
source, with its original embedding retained in the commuting square. -/
def HasParabolicImage (q : G ⟶ Q)
    {P : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ Q) : Prop :=
  ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (i : R ⟶ G) (p : R ⟶ P),
    IsParabolicSubgroup i ∧ Surjective p.hom.hom.left ∧ i ≫ q = p ≫ j

variable [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]

/-- If each Borel downstairs is the image of a Borel upstairs, the reduced inverse image
realizes each parabolic downstairs as the image of a parabolic upstairs. -/
theorem exists_parabolic_image_of_borel_realization (q : G ⟶ Q)
    (hq : Surjective q.hom.hom.left)
    (hlift : ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ Q),
      IsBorelSubgroup c → ∃ (B : GroupScheme (Spec (CommRingCat.of k)))
        (b : B ⟶ G) (f : B ⟶ C), IsBorelSubgroup b ∧
          Surjective f.hom.hom.left ∧ b ≫ q = f ≫ c)
    {P : GroupScheme (Spec (CommRingCat.of k))} (j : P ⟶ Q)
    (hj : IsParabolicSubgroup j) :
    HasParabolicImage q j := by
  let : Surjective q.hom.hom.left := hq
  let V := SubgroupPreimage.groupScheme q j
  have hV : IsClosedSubgroup (SubgroupPreimage.inclusion q j) :=
    SubgroupPreimage.isClosedSubgroup q j hj.isClosedSubgroup
  let : IsClosedImmersion (SubgroupPreimage.inclusion q j).hom.hom.left := hV
  let : LocallyOfFiniteType V.X.hom := by
    rw [← Over.w (SubgroupPreimage.inclusion q j).hom.hom]
    infer_instance
  let R := reducedSubgroup V
  let r : R ⟶ V := reducedSubgroupι V
  let i : R ⟶ G := r ≫ SubgroupPreimage.inclusion q j
  let p : R ⟶ P := r ≫ SubgroupPreimage.projection q j
  have hr : IsClosedSubgroup r :=
    inferInstanceAs (IsClosedImmersion (reducedSubgroupι V).hom.hom.left)
  have hi : IsClosedSubgroup i := hr.comp hV
  have hcomm : i ≫ q = p ≫ j := by
    change (r ≫ SubgroupPreimage.inclusion q j) ≫ q =
      (r ≫ SubgroupPreimage.projection q j) ≫ j
    rw [Category.assoc, subgroupIntersection_condition, Category.assoc]
  have hp : Surjective p.hom.hom.left := by
    let : Surjective r.hom.hom.left := ⟨ReducedSubgroup.redι_surjective V.X.left⟩
    let : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
      SubgroupPreimage.surjective_projection q j
    change Surjective (r.hom.hom.left ≫ (SubgroupPreimage.projection q j).hom.hom.left)
    infer_instance
  obtain ⟨C, c, a, hc, hac⟩ := hj.exists_isBorelSubgroup_factor
  obtain ⟨B, b, f, hb, hf, hbq⟩ := hlift C c hc
  let : Smooth B.X.hom := hb.smooth
  let : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k B.X.left B.X.hom
  have hbP : b ≫ q = (f ≫ a) ≫ j := by
    rw [Category.assoc, hac, hbq]
  let w : B ⟶ V := pullback.lift b (f ≫ a) hbP
  let wR : B ⟶ R := ReducedSubgroup.liftHom w
  have hwR : wR ≫ i = b := by
    change (ReducedSubgroup.liftHom w) ≫
      (reducedSubgroupι V ≫ SubgroupPreimage.inclusion q j) = b
    rw [← Category.assoc, ReducedSubgroup.liftHom_fac]
    exact pullback.lift_fst _ _ _
  have hpar : IsParabolicSubgroup i := by
    refine ⟨hi, inferInstanceAs (Smooth (reducedSubgroup V).X.hom), ?_⟩
    have : IsIso (toAlgebraicClosure k) :=
      isIso_SpecMap_iff.mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
    let F := GroupScheme.baseChange (toAlgebraicClosure k)
    exact ⟨F.obj B, F.map b, F.map wR, hb.baseChange_of_isIso (toAlgebraicClosure k), by
      rw [← F.map_comp, hwR]⟩
  exact ⟨R, i, p, hpar, hp, hcomm⟩

end Langlands.GroupScheme.QuotientSubgroupRealization
