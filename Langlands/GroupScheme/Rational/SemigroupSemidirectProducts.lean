import Langlands.GroupScheme.Rational.SemigroupSemidirectReduction

/-! # Exact ordered semigroup products under a semidirect lift -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {K G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom G.X.hom]
    [Smooth K.X.hom] [Smooth G.X.hom]
    [ConnectedSpace K.X.left] [ConnectedSpace G.X.left]
    (a : AutomorphicAction K G) (b : AutomorphicAction S.toGrp G)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (q : T ⟶ K.X) (g : T ⟶ G.X), b.act s (a.act q g) = a.act q (b.act s g))
    (hS : IsSplitTorus S.toGrp)

include hcomm hS

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- If zero is absent from the actual ambient support, the smooth connected
acting factor is the identity subgroup on every test. -/
theorem acting_top_eq_bot_of_zero_notMem_semidirect_support
    (hzero : 0 ∉ actionWeightSupport (a.semidirectLift b hcomm) ⊤) :
    (⊤ : SubgroupFunctor K) = ⊥ := by
  apply IsSmoothConnectedClosed.eq_bot_of_actionWeightSupport_eq_empty
    (AutomorphicAction.trivial S.toGrp K) hS
  · refine ⟨K, 𝟙 K, ⟨?_, SubgroupFunctor.range_id K⟩,
      IsClosedSubgroup.of_iso (Iso.refl K), inferInstance, inferInstance⟩
    change Mono (𝟙 K.X)
    infer_instance
  · intro T s q _
    exact Subgroup.mem_top _
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro χ hχ
    have heq : χ = 0 := Set.mem_singleton_iff.mp
      (actionWeightSupport_subset_zero_of_act_eq (AutomorphicAction.trivial S.toGrp K)
        (fun _ s q => AutomorphicAction.trivial_act S.toGrp K s q) hS ⊤ hχ)
    apply hzero
    exact heq ▸ actionWeightSupport_acting_subset_semidirect a b hcomm hχ

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- The acting coordinate is literally the identity point on every scheme
test when zero is absent from the ambient support. -/
theorem acting_points_eq_one_of_zero_notMem_semidirect_support
    (hzero : 0 ∉ actionWeightSupport (a.semidirectLift b hcomm) ⊤)
    (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ K.X) : q = 1 := by
  have hq : q ∈ (⊤ : SubgroupFunctor K).carrier T := Subgroup.mem_top _
  rw [acting_top_eq_bot_of_zero_notMem_semidirect_support a b hcomm hS hzero] at hq
  exact hq

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- When the ambient zero weight is absent, the canonical normal inclusion
is an isomorphism of schemes over the original field. -/
theorem isIso_semidirectInl_of_zero_notMem_support
    (hzero : 0 ∉ actionWeightSupport (a.semidirectLift b hcomm) ⊤) :
    IsIso a.semidirectInl.hom.hom := by
  rw [isIso_iff_yoneda_map_bijective]
  intro T
  constructor
  · intro x y hxy
    exact (inferInstance : Mono a.semidirectInl.hom.hom).right_cancellation _ _ hxy
  · intro z
    refine ⟨(a.semidirectPointsEquiv T z).left, ?_⟩
    have hd := a.semidirect_point_decomposition z
    rw [acting_points_eq_one_of_zero_notMem_semidirect_support a b hcomm hS hzero
      T (a.semidirectPointsEquiv T z).right, MonObj.one_comp, mul_one] at hd
    exact hd.symm

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- The canonical normal-factor scheme isomorphism in the zero-absent case. -/
def semidirectNormalIsoOfZeroNotMem
    (hzero : 0 ∉ actionWeightSupport (a.semidirectLift b hcomm) ⊤) :
    G.X ≅ a.semidirectProduct.X :=
  letI := isIso_semidirectInl_of_zero_notMem_support a b hcomm hS hzero
  asIso a.semidirectInl.hom.hom

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- With no ambient zero weight, every point lies in the normal factor. -/
theorem range_semidirectInl_eq_top_of_zero_notMem_support
    (hzero : 0 ∉ actionWeightSupport (a.semidirectLift b hcomm) ⊤) :
    SubgroupFunctor.range a.semidirectInl = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro z
  constructor
  · exact fun _ => Subgroup.mem_top _
  · intro _
    apply (a.mem_range_semidirectInl_iff z).mpr
    exact acting_points_eq_one_of_zero_notMem_semidirect_support a b hcomm hS hzero T _

/-- The exact ordered-product property passes from the normal action to its
actual semidirect lift. Only global functoriality and the local inverse-image equalities along the
normal inclusion remain as comparison premises. Inner stability and the
zero-weight alternatives are derived. -/
theorem hasOrderedSemigroupProducts_semidirect_of_comap
    (hfun : SemigroupFunctorialityStatement.{u})
    (hcomap : ∀ A : AddSubsemigroup (characterLattice S),
      (semigroupSubgroup (a.semidirectLift b hcomm) A).comap a.semidirectInl =
        semigroupSubgroup b A)
    (hb : HasOrderedSemigroupProducts b) :
    HasOrderedSemigroupProducts (a.semidirectLift b hcomm) := by
  intro n Ψ hcover hdis hcross
  by_cases hzero : 0 ∈ actionWeightSupport (a.semidirectLift b hcomm) ⊤
  · exact semigroupOrderedSemidirect_of_larger_support_of_comap a b hcomm hS hfun hcomap hb
      (semigroupSubgroup_isStable_inner_of_comap a b hcomm hS hcomap)
      (actionWeightSupport (a.semidirectLift b hcomm) ⊤)
      (actionWeightSupport_normal_subset_semidirect a b hcomm) hzero n Ψ hcover hdis hcross
  · obtain ⟨H, j, hj, hprod⟩ := hb.for_larger_support
      (actionWeightSupport (a.semidirectLift b hcomm) ⊤)
      (actionWeightSupport_normal_subset_semidirect a b hcomm) n Ψ hcover hdis hcross
    have htop := range_semidirectInl_eq_top_of_zero_notMem_support a b hcomm hS hzero
    let : IsIso (orderedMultiplication j) := hprod
    let : IsIso a.semidirectInl.hom.hom :=
      isIso_semidirectInl_of_zero_notMem_support a b hcomm hS hzero
    refine ⟨H, fun i => j i ≫ a.semidirectInl, ?_, ?_⟩
    · intro i
      have hr := (hj i).1.comp
        (show (SubgroupFunctor.range a.semidirectInl).IsRepresentedBy a.semidirectInl from
          ⟨inferInstance, rfl⟩)
      rw [semigroupSubgroup_map_eq a.semidirectInl a.isClosedSubgroup_semidirectInl
        b (a.semidirectLift b hcomm)
        (fun _ s g => (a.semidirectLift_inl b hcomm s g).symm)
        (AddSubsemigroup.closure (Ψ i)) (by
          rw [htop]
          exact fun _ _ _ => Subgroup.mem_top _)] at hr
      exact ⟨hr, (hj i).2.1.comp a.isClosedSubgroup_semidirectInl,
        (hj i).2.2.1, (hj i).2.2.2⟩
    · rw [← orderedMultiplication_comp]
      infer_instance

/-- The original full-intersection interface for semidirect products. -/
theorem hasOrderedSemigroupProducts_semidirect
    (hfun : SemigroupFunctorialityStatement.{u})
    (hinter : SemigroupIntersectionStatement.{u})
    (hb : HasOrderedSemigroupProducts b) :
    HasOrderedSemigroupProducts (a.semidirectLift b hcomm) := by
  exact hasOrderedSemigroupProducts_semidirect_of_comap a b hcomm hS hfun
    (semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter) hb

end Langlands.GroupScheme.RelativeRoot
