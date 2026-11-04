import Langlands.GroupScheme.Adjoint.CenterQuotientEnvelope
import Langlands.GroupScheme.Adjoint.CenterQuotientCommutator
import Langlands.GroupScheme.HomogeneousClosedImmersion
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.RepresentedAction

/-! # The geometric core of the centre-quotient theorem

Over an algebraically closed field, let `q : G ⟶ Q` be an fppf quotient of a smooth connected
affine group `G` with trivial unipotent radical by its full centre. A nontrivial smooth
connected unipotent normal subgroup `U` of `Q` would contain a nontrivial smooth connected
central subgroup `Z` stable under conjugation by `Q`. Its preimage in `G` is a closed normal
subgroup whose rational points commute (`commute_of_lift`), so its rational points are central
in `G` (`mem_center_of_isNormal_of_commute`). Rational points of `Z` lift to `G`, so they are
all trivial, and `Z` is trivial, a contradiction. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CenterQuotient

section Trivial

variable {S : Scheme.{u}} {U Q : GroupScheme S}

/-- If the range of the identity of `U` is trivial, the identity morphism of `U.X` is `1`. -/
theorem id_eq_one_of_range_id_eq_bot (h : SubgroupFunctor.range (𝟙 U) = ⊥) :
    𝟙 U.X = (1 : U.X ⟶ U.X) := by
  have h1 : 𝟙 U.X ≫ (𝟙 U : U ⟶ U).hom.hom ∈ (SubgroupFunctor.range (𝟙 U)).carrier U.X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, rfl⟩
  rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Category.id_comp, Grp.id_hom_hom] at h1
  exact h1

/-- If the identity morphism of `U.X` is `1`, every homomorphism out of `U` has trivial
range. -/
theorem range_eq_bot_of_id_eq_one (j : U ⟶ Q) (h : 𝟙 U.X = (1 : U.X ⟶ U.X)) :
    SubgroupFunctor.range j = ⊥ := by
  ext T x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨y, rfl⟩
    have hy : y = 1 := by
      rw [← Category.comp_id y, h, MonObj.comp_one]
    rw [hy, MonObj.one_comp]
  · rintro rfl
    exact Subgroup.one_mem _

end Trivial

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **The geometric core.** Over an algebraically closed field, the target of an fppf quotient
of a smooth connected affine group with trivial unipotent radical by its full centre, with
affine target locally of finite type, has trivial unipotent radical. -/
theorem hasTrivialUnipotentRadical_of_isFppfQuotient_center
    {G Q : GroupScheme (Spec (CommRingCat.of K))} (q : G ⟶ Q) (hGs : Smooth G.X.hom)
    (hGa : IsAffineHom G.X.hom) (hGc : ConnectedSpace G.X.left)
    (hG : HasTrivialUnipotentRadical G) (hQa : IsAffineHom Q.X.hom)
    (hQf : LocallyOfFiniteType Q.X.hom) (hq : RelativeRoot.IsFppfQuotient (center G) q) :
    HasTrivialUnipotentRadical Q := by
  intro U j hj hUs hUc hUu hUn
  by_contra hne
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  -- A nontrivial smooth connected central subgroup `Z` of `U`, stable under conjugation.
  let c : AutomorphicAction Q Q := AutomorphicAction.conjugation (𝟙 Q)
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have hstab : c.IsStable (SubgroupFunctor.range j) := by
    intro T g y hy
    rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
    exact hUn T g y (Subgroup.mem_top _) hy
  let b := c.onRepresentedSubgroup j hrep hstab
  have hne' : SubgroupFunctor.range (𝟙 U) ≠ ⊥ := fun h =>
    hne (range_eq_bot_of_id_eq_one j (id_eq_one_of_range_id_eq_bot h))
  obtain ⟨Z, z, -, hz, hZs, hZa, -, -, hzcen, hzst, hzne, -⟩ :=
    hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent b hQa hne' hUu
  have : IsClosedImmersion z.hom.hom.left := hz
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  have hzj : IsClosedSubgroup (z ≫ j) := by
    change IsClosedImmersion (z.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  -- Its image in `Q` is normal.
  have hzjn : (SubgroupFunctor.range (z ≫ j)).IsNormal := by
    intro T g y _ hy
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    have hv : v ≫ z.hom.hom ∈ (SubgroupFunctor.range z).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp (hzst T g _ hv)
    refine SubgroupFunctor.mem_range.mpr ⟨w, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc w, hw,
      AutomorphicAction.onRepresentedSubgroup_act_comp, AutomorphicAction.conjugation_act,
      Grp.id_hom_hom, Category.comp_id, Category.assoc]
  -- The preimage `A` of `Z` in `G` is closed and normal, and its rational points commute.
  let a := SubgroupPreimage.inclusion q (z ≫ j)
  let π := SubgroupPreimage.projection q (z ≫ j)
  have ha : IsClosedSubgroup a := SubgroupPreimage.isClosedSubgroup q (z ≫ j) hzj
  have han : (SubgroupFunctor.range a).IsNormal := SubgroupPreimage.isNormal q (z ≫ j) hzjn
  have e : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (SubgroupPreimage.groupScheme q (z ≫ j)).X,
      (x ≫ a.hom.hom) ≫ q.hom.hom = ((x ≫ π.hom.hom) ≫ z.hom.hom) ≫ j.hom.hom := by
    intro x
    simp only [Category.assoc]
    rw [(SubgroupPreimage.isPullback q (z ≫ j)).w, Grp.comp_hom_hom]
  have hcomm : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (SubgroupPreimage.groupScheme q (z ≫ j)).X, Commute (x ≫ a.hom.hom) (y ≫ a.hom.hom) :=
    fun x y => commute_of_lift q j hq hG hUu (e x) (e y) (hzcen _ _)
  have hcen := mem_center_of_isNormal_of_commute hG a ha han hcomm
  -- Rational points of `Z` lift to the preimage, so they are trivial.
  have : Surjective q.hom.hom.left := hq.2.1
  have hZpt : ∀ w : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Z.X, w = 1 := by
    intro w
    obtain ⟨g, hg⟩ := HomogeneousClosedImmersion.exists_rational_lift q.hom.hom
      (w ≫ z.hom.hom ≫ j.hom.hom) (q.hom.hom.left.surjective _)
    have hgw : g ≫ q.hom.hom = w ≫ (z ≫ j).hom.hom := by
      rw [hg, Grp.comp_hom_hom]
    have hx : (SubgroupPreimage.isPullback q (z ≫ j)).lift g w hgw ≫ a.hom.hom = g :=
      (SubgroupPreimage.isPullback q (z ≫ j)).lift_fst _ _ _
    have h1 := hcen ((SubgroupPreimage.isPullback q (z ≫ j)).lift g w hgw)
    rw [hx, ← hq.2.2.2, mem_range_kernelι_iff, hg] at h1
    apply (cancel_mono (z.hom.hom ≫ j.hom.hom)).mp
    rw [h1, MonObj.one_comp]
  -- Hence `Z` is trivial.
  have : IsReduced Z.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K
      Z.X.left Z.X.hom
  have hid : 𝟙 Z.X = (1 : Z.X ⟶ Z.X) := hom_ext_rationalPoints fun w => by
    rw [Category.comp_id, MonObj.comp_one]
    exact hZpt w
  exact hzne (range_eq_bot_of_id_eq_one z hid)

end Langlands.GroupScheme.CenterQuotient
