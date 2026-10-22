import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup of an open subgroup, viewed as an actual open subgroup of the ambient group. -/
def ambientOpenSubgroup (H : OpenSubgroup G) (K : OpenSubgroup H) : OpenSubgroup G where
  toSubgroup := K.toSubgroup.map H.toSubgroup.subtype
  isOpen' := H.isOpen.isOpenMap_subtype_val _ K.isOpen

omit [IsTopologicalGroup G] in
theorem ambientOpenSubgroup_le (H : OpenSubgroup G) (K : OpenSubgroup H) :
    (ambientOpenSubgroup H K).toSubgroup ≤ H.toSubgroup := by
  rintro x ⟨y, hy, rfl⟩
  exact y.2

/-- The normal core of an open subgroup in a compact group is open. -/
def ambientOpenNormalCore [CompactSpace G] (H : OpenSubgroup G) : OpenNormalSubgroup G := by
  have : Finite (G ⧸ H.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen H.toSubgroup H.isOpen
  have : H.toSubgroup.FiniteIndex := H.finiteIndex_of_finite_quotient
  exact
    { toSubgroup := H.toSubgroup.normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (H.normalCore_isClosed H.isClosed) }

theorem ambientOpenNormalCore_le [CompactSpace G] (H : OpenSubgroup G) :
    (ambientOpenNormalCore H).toSubgroup ≤ H.toSubgroup :=
  H.normalCore_le

/-- Pull an ambient open normal subgroup back to the subgroup with its inherited topology. -/
def restrictOpenNormal (H : OpenSubgroup G) (N : OpenNormalSubgroup G) :
    OpenNormalSubgroup H where
  toOpenSubgroup := N.toOpenSubgroup.comap H.toSubgroup.subtype continuous_subtype_val
  isNormal' := by
    change (N.toSubgroup.comap H.toSubgroup.subtype).Normal
    infer_instance

/-- Every open normal subgroup of H contains the restriction of an ambient normal subgroup
that already lies in H. -/
theorem exists_ambient_openNormal [CompactSpace G] (H : OpenSubgroup G)
    (K : OpenNormalSubgroup H) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ H.toSubgroup ∧ restrictOpenNormal H N ≤ K := by
  let U := ambientOpenSubgroup H K.toOpenSubgroup
  let N := ambientOpenNormalCore U
  have hN : N.toSubgroup ≤ U.toSubgroup := ambientOpenNormalCore_le U
  refine ⟨N, hN.trans (ambientOpenSubgroup_le H K.toOpenSubgroup), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hN hx
  have h : y = x := Subtype.ext hxy
  change y ∈ K at hy
  exact h ▸ hy

/-- A fixed ambient core forces every transfer index to lie in H. -/
def transferIndex [CompactSpace G] (H : OpenSubgroup G)
    (N : FiniteQuotientIndex (G := G)) : FiniteQuotientIndex (G := H) :=
  OrderDual.toDual (restrictOpenNormal H (ambientOpenNormalCore H ⊓ OrderDual.ofDual N))

theorem transferIndex_monotone [CompactSpace G] (H : OpenSubgroup G) :
    Monotone (transferIndex H) := by
  intro N M h x hx
  exact ⟨hx.1, h hx.2⟩

/-- The genuine refinement functor used to compute subgroup cohomology at ambient finite stages. -/
def transferIndexFunctor [CompactSpace G] (H : OpenSubgroup G) :
    FiniteQuotientIndex (G := G) ⥤ FiniteQuotientIndex (G := H) :=
  (transferIndex_monotone H).functor

instance transferIndexFunctor_final [CompactSpace G] (H : OpenSubgroup G) :
    (transferIndexFunctor H).Final := by
  apply (Monotone.final_functor_iff (transferIndex_monotone H)).mpr
  intro K
  obtain ⟨N, hNH, hNK⟩ := exists_ambient_openNormal H (OrderDual.ofDual K)
  refine ⟨OrderDual.toDual N, ?_⟩
  intro x hx
  exact hNK hx.2

end Langlands.Continuous

/- Development component: QuotientSubgroup. -/
open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [Group G]

/-- The actual inclusion of the subgroup's normal quotient into the ambient normal quotient. -/
def quotientSubgroupMap (H N : Subgroup G) [N.Normal] :
    H ⧸ N.comap H.subtype →* G ⧸ N :=
  QuotientGroup.map (N.comap H.subtype) N H.subtype (fun _ hx => hx)

theorem quotientSubgroupMap_injective (H N : Subgroup G) [N.Normal] :
    Function.Injective (quotientSubgroupMap H N) := by
  intro x y
  refine QuotientGroup.induction_on x (fun x => ?_)
  refine QuotientGroup.induction_on y (fun y h => ?_)
  apply QuotientGroup.eq.mpr
  change (x.1 : G ⧸ N) = (y.1 : G ⧸ N) at h
  change x.1⁻¹ * y.1 ∈ N
  exact QuotientGroup.eq.mp h

/-- Codomain restriction to the actual image subgroup in the finite quotient. -/
def quotientSubgroupToImage (H N : Subgroup G) [N.Normal] :
    H ⧸ N.comap H.subtype →* H.map (QuotientGroup.mk' N) where
  toFun q := ⟨quotientSubgroupMap H N q, by
    refine QuotientGroup.induction_on q (fun g => ?_)
    exact ⟨g.1, g.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (quotientSubgroupMap H N))
  map_mul' x y := Subtype.ext (map_mul (quotientSubgroupMap H N) x y)

/-- The subgroup quotient and its image in the ambient quotient are explicitly isomorphic. -/
noncomputable def quotientSubgroupEquiv (H N : Subgroup G) [N.Normal] :
    H ⧸ N.comap H.subtype ≃* H.map (QuotientGroup.mk' N) :=
  MulEquiv.ofBijective (quotientSubgroupToImage H N) ⟨
    fun _ _ h => quotientSubgroupMap_injective H N (congrArg Subtype.val h),
    by
      rintro ⟨q, g, hg, rfl⟩
      exact ⟨((⟨g, hg⟩ : H) : H ⧸ N.comap H.subtype), Subtype.ext rfl⟩⟩

/-- Quotienting by a normal subgroup contained in H preserves its index. -/
theorem quotientSubgroup_index (H N : Subgroup G) [N.Normal] (hNH : N ≤ H) :
    (H.map (QuotientGroup.mk' N)).index = H.index :=
  H.index_map_eq (QuotientGroup.mk'_surjective N) (by
    simpa only [QuotientGroup.ker_mk'] using hNH)

/-- Restriction preserves the actual fixed coefficient module when N lies in H. -/
def fixedRestrictionEquiv (A : Rep.{u} k G) (H N : Subgroup G) (hNH : N ≤ H) :
    Representation.invariants (A.ρ.comp N.subtype) ≃ₗ[k]
      Representation.invariants ((A.ρ.comp H.subtype).comp (N.comap H.subtype).subtype) where
  toFun x := ⟨x.1, fun n => x.2 ⟨n.1.1, n.2⟩⟩
  invFun x := ⟨x.1, fun n => x.2 ⟨⟨n.1, hNH n.2⟩, n.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The fixed-coefficient equivalence intertwines the two genuine quotient actions. -/
noncomputable def quotientRestrictionIso (A : Rep.{u} k G) (H N : Subgroup G)
    [N.Normal] (hNH : N ≤ H) :
    Rep.res (quotientSubgroupMap H N) (A.quotientToInvariants N) ≅
      (Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype) :=
  Rep.mkIso (Representation.Equiv.mk (fixedRestrictionEquiv A H N hNH) (by
    intro q
    refine QuotientGroup.induction_on q (fun g => ?_)
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl))

end Langlands.Continuous
