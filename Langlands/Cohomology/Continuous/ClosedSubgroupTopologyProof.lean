import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof
import Langlands.Cohomology.Continuous.ClosedSubgroupTopologyStatement

universe u

namespace Langlands.Continuous

variable {G Y : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace Y] [DiscreteTopology Y]

/-- Ambient open normal subgroups refine every open subgroup of a subgroup. -/
theorem exists_ambient_normal_refinement (H : Subgroup G) (K : OpenSubgroup H) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup.comap H.subtype ≤ K.toSubgroup := by
  obtain ⟨V, hV, hVK⟩ := isOpen_induced_iff.mp K.isOpen
  have h1 : (1 : G) ∈ V := by
    have : (1 : H) ∈ Subtype.val ⁻¹' V := by rw [hVK]; exact K.one_mem
    exact this
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨N, ?_⟩
  intro x hx
  have : x ∈ Subtype.val ⁻¹' V := hN hx
  rwa [hVK] at this

/-- Every discrete-valued continuous tuple map on a closed subgroup extends to ambient tuples. -/
theorem exists_closedSubgroup_tuple_extension (H : ClosedSubgroup G) (n : ℕ)
    (f : C((Fin n → H), Y)) :
    ∃ F : C((Fin n → G), Y), ∀ x : Fin n → H,
      F (fun i => (x i : G)) = f x := by
  classical
  let : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  obtain ⟨K, F, hF⟩ := exists_finite_quotient_factor n f f.continuous
  obtain ⟨N, hN⟩ := exists_ambient_normal_refinement H.toSubgroup K.toOpenSubgroup
  let π : (Fin n → H) → (Fin n → G ⧸ N.toSubgroup) :=
    fun x i => ((x i : G) : G ⧸ N.toSubgroup)
  have hf : (f : (Fin n → H) → Y).FactorsThrough π := by
    intro x y hxy
    rw [← hF x, ← hF y]
    congr 1
    funext i
    apply QuotientGroup.eq.mpr
    apply hN
    change (x i : G)⁻¹ * (y i : G) ∈ N.toSubgroup
    exact QuotientGroup.eq.mp (congrFun hxy i)
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.isOpen
  let Q : C((Fin n → G ⧸ N.toSubgroup), Y) :=
    ⟨Function.extend π f (fun _ => f (fun _ => 1)), continuous_of_discreteTopology⟩
  refine ⟨⟨fun x => Q (fun i => (x i : G ⧸ N.toSubgroup)),
    Q.continuous.comp (continuous_pi fun i =>
      QuotientGroup.continuous_mk.comp (continuous_apply i))⟩, ?_⟩
  intro x
  exact hf.extend_apply (fun _ => f (fun _ => 1)) x

omit [TotallyDisconnectedSpace G] in
/-- Equality on closed normal subgroup tuples holds on a suitable open normal supergroup. -/
theorem exists_openNormal_tuple_agreement (H : ClosedSubgroup G) [H.toSubgroup.Normal]
    (n : ℕ) (f g : C((Fin n → G), Y))
    (hfg : ∀ x : Fin n → H, f (fun i => (x i : G)) = g (fun i => (x i : G))) :
    ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
      ∀ x : Fin n → G, (∀ i, x i ∈ U) → f x = g x := by
  classical
  obtain ⟨N, F, hF⟩ := exists_finite_quotient_factor n
    (fun x => (f x, g x)) (f.continuous.prodMk g.continuous)
  let U : OpenNormalSubgroup G :=
    { toSubgroup := H.toSubgroup ⊔ N.toSubgroup
      isOpen' := Subgroup.isOpen_mono le_sup_right N.isOpen
      isNormal' := inferInstance }
  refine ⟨U, le_sup_left, ?_⟩
  intro x hx
  have hrep (i : Fin n) : ∃ h ∈ H.toSubgroup, ∃ t ∈ N.toSubgroup, h * t = x i :=
    Subgroup.mem_sup_of_normal_right.mp (hx i)
  choose h hh t ht heq using hrep
  let y : Fin n → H := fun i => ⟨h i, hh i⟩
  have hquot : (fun i => (x i : G ⧸ N.toSubgroup)) =
      (fun i => ((y i : G) : G ⧸ N.toSubgroup)) := by
    funext i
    rw [← heq i, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (ht i), mul_one]
  have hval : (f x, g x) = (f (fun i => (y i : G)), g (fun i => (y i : G))) := by
    rw [← hF x, ← hF (fun i => (y i : G)), hquot]
  exact (congrArg Prod.fst hval).trans ((hfg y).trans (congrArg Prod.snd hval).symm)

/-- The exact published finite-tuple approximation proposition. -/
theorem closedSubgroupTupleApproximation : ClosedSubgroupTupleApproximation.{u} := by
  constructor
  · intro G _ _ _ _ _ _ Y _ _ H n f
    exact exists_closedSubgroup_tuple_extension H n f
  · intro G _ _ _ _ _ _ Y _ _ H hH n f g hfg
    let : H.toSubgroup.Normal := hH
    exact exists_openNormal_tuple_agreement H n f g hfg

end Langlands.Continuous
