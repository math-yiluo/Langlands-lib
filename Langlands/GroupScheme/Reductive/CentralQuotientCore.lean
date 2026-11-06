import Langlands.GroupScheme.Adjoint.CenterQuotientCore
import Langlands.GroupScheme.Reductive.CentralQuotientCommutator
import Langlands.GroupScheme.Reductive.CentralPreimageTrivial

/-! # The geometric core of the central-quotient theorem

Over an algebraically closed field, let `q : G ⟶ Q` be an fppf quotient of a smooth connected
affine group `G` with trivial unipotent radical by a subgroup functor `N ≤ center G`. A
nontrivial smooth connected unipotent normal subgroup `U` of `Q` would contain a nontrivial
smooth connected central subgroup `Z` stable under conjugation by `Q`. As in the full-centre
case, the rational points of the preimage `A` of `Z` in `G` are central in `G`. The identity
component `M` of the reduced subgroup of `A` is then a central smooth connected subgroup of
`G`, so its image in the unipotent group `U` has finitely many rational points; since `M(K)`
has finite index in `A(K)` and `A(K)` maps onto `Z(K)`, the group `Z(K)` is finite, so the
smooth connected group `Z` is trivial, a contradiction. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralQuotient

open CenterQuotient

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **Finiteness of `Z(K)`.** Let `a : A ⟶ G` be a closed embedding of an affine group of
finite type into a smooth affine group with trivial unipotent radical, all of whose rational
points are central in `G`, and let `π : A ⟶ Z` be surjective on rational points, followed by
a closed embedding `z : Z ⟶ U` into an affine unipotent group. Then `Z` has finitely many
rational points. -/
theorem finite_rationalPoints_of_central_preimage
    {G A Z U : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : HasTrivialUnipotentRadical G)
    [IsAffineHom A.X.hom] [LocallyOfFiniteType A.X.hom] (a : A ⟶ G) [Mono a.hom.hom]
    (hcen : ∀ x : rationalPoints A, x ≫ a.hom.hom ∈ (center G).carrier _)
    [IsAffineHom U.X.hom] (hU : IsUnipotent U) (π : A ⟶ Z) (z : Z ⟶ U) [Mono z.hom.hom]
    (hπ : Function.Surjective (rationalPoints.map π)) : Finite (rationalPoints Z) := by
  have : Smooth (reducedSubgroup A).X.hom := ReducedSubgroup.smooth_reducedSubgroup A
  have : IsAffineHom (reducedSubgroup A).X.hom := ReducedSubgroup.isAffineHom_reducedSubgroup A
  have : Mono (reducedSubgroupι A).hom.hom := inferInstanceAs (Mono (ReducedSubgroup.redOverι A))
  have : Mono (identityComponentι (reducedSubgroup A) ≫ reducedSubgroupι A ≫ a).hom.hom := by
    change Mono ((identityComponentι (reducedSubgroup A)).hom.hom ≫
      (reducedSubgroupι A).hom.hom ≫ a.hom.hom)
    infer_instance
  -- The identity component of the reduced preimage is central in `G`.
  have hmc : IsCentral (identityComponentι (reducedSubgroup A) ≫ reducedSubgroupι A ≫ a) :=
    isCentral_of_rationalPoints _ fun x => by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        hcen (x ≫ (identityComponentι (reducedSubgroup A)).hom.hom ≫
          (reducedSubgroupι A).hom.hom)
  -- Its image in `U` has finitely many rational points.
  have hfin := finite_range_of_isCentral hG _ hmc hU
    (identityComponentι (reducedSubgroup A) ≫ reducedSubgroupι A ≫ π ≫ z)
  have : Finite (Set.range (rationalPoints.map
      (identityComponentι (reducedSubgroup A) ≫ reducedSubgroupι A ≫ π ≫ z))) :=
    hfin.to_subtype
  have := finiteIndex_map_rationalIdentitySubgroup A
  have hR : Finite (rationalPoints.map (π ≫ z)).range := by
    refine finite_range_of_finite_map _
      ((IdentityComponent.rationalIdentitySubgroup (reducedSubgroup A)).map
        (rationalPoints.map (reducedSubgroupι A))) ?_
    refine Finite.Set.subset (Set.range (rationalPoints.map
      (identityComponentι (reducedSubgroup A) ≫ reducedSubgroupι A ≫ π ≫ z))) ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨w, rfl⟩ := (IdentityComponent.mem_rationalIdentitySubgroup (reducedSubgroup A) x).1 hx
    refine ⟨w, ?_⟩
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  -- Rational points of `Z` embed into this finite image.
  refine Finite.of_injective (fun w : rationalPoints Z =>
    (⟨rationalPoints.map z w, ?_⟩ : (rationalPoints.map (π ≫ z)).range)) ?_
  · obtain ⟨x, hx⟩ := hπ w
    refine ⟨x, ?_⟩
    rw [← hx, rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
      Grp.comp_hom_hom, Category.assoc]
  · intro w w' h
    exact (cancel_mono z.hom.hom).1 (congrArg Subtype.val h)

/-- **The geometric core.** Over an algebraically closed field, the target of an fppf quotient
of a smooth connected affine group with trivial unipotent radical by a subgroup functor
contained in its centre, with affine target locally of finite type, has trivial unipotent
radical. -/
theorem hasTrivialUnipotentRadical_of_isFppfQuotient
    {G Q : GroupScheme (Spec (CommRingCat.of K))} (q : G ⟶ Q) {N : SubgroupFunctor G}
    (hGs : Smooth G.X.hom) (hGa : IsAffineHom G.X.hom) (hGc : ConnectedSpace G.X.left)
    (hG : HasTrivialUnipotentRadical G) (hQa : IsAffineHom Q.X.hom)
    (hQf : LocallyOfFiniteType Q.X.hom) (hN : N ≤ center G)
    (hq : RelativeRoot.IsFppfQuotient N q) :
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
  obtain ⟨Z, z, -, hz, hZs, hZa, -, hZc, hzcen, hzst, hzne, -⟩ :=
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
  -- The preimage `A` of `Z` in `G` is closed and normal, and its rational points are central.
  have ha : IsClosedSubgroup (SubgroupPreimage.inclusion q (z ≫ j)) :=
    SubgroupPreimage.isClosedSubgroup q (z ≫ j) hzj
  have han : (SubgroupFunctor.range (SubgroupPreimage.inclusion q (z ≫ j))).IsNormal :=
    SubgroupPreimage.isNormal q (z ≫ j) hzjn
  have e : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (SubgroupPreimage.groupScheme q (z ≫ j)).X,
      (x ≫ (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom) ≫ q.hom.hom =
        ((x ≫ (SubgroupPreimage.projection q (z ≫ j)).hom.hom) ≫ z.hom.hom) ≫ j.hom.hom := by
    intro x
    simp only [Category.assoc]
    rw [(SubgroupPreimage.isPullback q (z ≫ j)).w, Grp.comp_hom_hom]
  have hcomm : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (SubgroupPreimage.groupScheme q (z ≫ j)).X,
      Commute (x ≫ (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom)
        (y ≫ (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom) :=
    fun x y => commute_of_lift q j hq hN hG hUu (e x) (e y) (hzcen _ _)
  have hcen := mem_center_of_isNormal_of_commute hG _ ha han hcomm
  -- Rational points of `Z` lift to the preimage.
  have : Surjective q.hom.hom.left := hq.2.1
  have hπ : Function.Surjective (rationalPoints.map (SubgroupPreimage.projection q (z ≫ j))) := by
    intro w
    obtain ⟨g, hg⟩ := HomogeneousClosedImmersion.exists_rational_lift q.hom.hom
      (w ≫ z.hom.hom ≫ j.hom.hom) (q.hom.hom.left.surjective _)
    have hgw : g ≫ q.hom.hom = w ≫ (z ≫ j).hom.hom := by
      rw [hg, Grp.comp_hom_hom]
    exact ⟨(SubgroupPreimage.isPullback q (z ≫ j)).lift g w hgw,
      (SubgroupPreimage.isPullback q (z ≫ j)).lift_snd _ _ _⟩
  -- Hence `Z(K)` is finite, and `Z` is trivial.
  have : IsClosedImmersion (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom.left := ha
  have : Mono (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom (SubgroupPreimage.groupScheme q (z ≫ j)).X.hom := by
    rw [← Over.w (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom]
    infer_instance
  have : LocallyOfFiniteType (SubgroupPreimage.groupScheme q (z ≫ j)).X.hom := by
    rw [← Over.w (SubgroupPreimage.inclusion q (z ≫ j)).hom.hom]
    infer_instance
  have : Finite (rationalPoints Z) :=
    finite_rationalPoints_of_central_preimage hG (SubgroupPreimage.inclusion q (z ≫ j)) hcen
      hUu (SubgroupPreimage.projection q (z ≫ j)) z hπ
  exact hzne (range_eq_bot_of_id_eq_one z (id_eq_one_of_finite_rationalPoints Z))

end Langlands.GroupScheme.CentralQuotient
