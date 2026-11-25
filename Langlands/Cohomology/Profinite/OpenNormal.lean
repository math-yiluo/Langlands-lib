import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Torsor
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Open normal subgroups of a profinite group

Basic facts on the open normal subgroups of a topological group that the cohomology of
profinite groups uses throughout: they form a nonempty family, their quotients are discrete
(and finite when the group is compact), and in a compact totally disconnected group they form
a basis of neighbourhoods of the identity, also in every finite power of the group. As a
consequence a locally constant function on `G^ι` (`ι` finite) is constant on the cosets of
`U^ι` for some open normal subgroup `U`, and so factors through `(G/U)^ι`.
-/

namespace Langlands.ProfiniteCohomology

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace OpenNormalSubgroup

instance instNonempty : Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤, isNormal' := ⟨fun _ _ _ => Set.mem_univ _⟩ }⟩

theorem mem_nhds_one (U : OpenNormalSubgroup G) : (U : Set G) ∈ 𝓝 (1 : G) :=
  U.toOpenSubgroup.isOpen.mem_nhds U.one_mem

variable [IsTopologicalGroup G]

instance discreteTopology_quotient (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen

instance finite_quotient [CompactSpace G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem hasBasis_nhds_one :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup G => True) (fun U => (U : Set G)) := by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨U, _, hU⟩ => mem_of_superset U.mem_nhds_one hU⟩⟩
  obtain ⟨t, hts, ht, h1⟩ := mem_nhds_iff.mp hs
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1
  exact ⟨U, trivial, hU.trans hts⟩

theorem hasBasis_nhds_one_pi (ι : Type*) [Finite ι] :
    (𝓝 (1 : ι → G)).HasBasis (fun _ : OpenNormalSubgroup G => True)
      (fun U => Set.univ.pi fun _ => (U : Set G)) := by
  simp only [nhds_pi, Pi.one_apply]
  refine (hasBasis_nhds_one.pi_self (ι := ι)).to_hasBasis ?_ ?_
  · rintro ⟨I, U⟩ -
    exact ⟨U, trivial, fun x hx i _ => hx i (Set.mem_univ i)⟩
  · intro U _
    exact ⟨⟨Set.univ, U⟩, ⟨Set.finite_univ, trivial⟩, subset_rfl⟩

end OpenNormalSubgroup

section Factor

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_openNormalSubgroup_pi_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : ι → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y := by

  let O : OpenNormalSubgroup G → Set (ι → G) := fun U =>
    {y | ∀ y' : ι → G, (∀ i, (y i)⁻¹ * y' i ∈ U) → f y' = f y}
  have hO : ∀ U, IsOpen (O U) := by
    intro U
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hopen : IsOpen ((fun w : ι → G => fun i => (y i)⁻¹ * w i) ⁻¹'
        Set.univ.pi fun _ => (U : Set G)) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => U.toOpenSubgroup.isOpen).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))
    refine mem_of_superset (hopen.mem_nhds fun i _ => by simp) ?_
    intro w hw y' hy'
    have hw' : ∀ i, (y i)⁻¹ * w i ∈ U := fun i => hw i (Set.mem_univ i)
    have h1 : f y' = f y := hy y' fun i => by
      have := mul_mem (hw' i) (hy' i)
      rwa [mul_assoc, mul_inv_cancel_left] at this
    rw [h1, hy w hw']
  have hcover : Set.univ ⊆ ⋃ U, O U := by
    intro x _
    have hS : (fun w : ι → G => fun i => x i * w i) ⁻¹' (f ⁻¹' {f x}) ∈ 𝓝 (1 : ι → G) :=
      ((hf.isOpen_fiber (f x)).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).mem_nhds
        (by simp)
    obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one_pi ι).mem_iff.mp hS
    refine Set.mem_iUnion.mpr ⟨U, fun y' hy' => ?_⟩
    have := hU (show (fun i => (x i)⁻¹ * y' i) ∈ Set.univ.pi fun _ => (U : Set G) from
      fun i _ => hy' i)
    simpa using this
  have hdir : Directed (· ⊆ ·) O := fun U V =>
    ⟨U ⊓ V, fun y hy y' hy' => hy y' fun i => (hy' i).1,
      fun y hy y' hy' => hy y' fun i => (hy' i).2⟩
  obtain ⟨U, hU⟩ := isCompact_univ.elim_directed_cover O hO hcover hdir
  exact ⟨U, fun x y hxy => (hU (Set.mem_univ x) y hxy).symm⟩

theorem exists_openNormalSubgroup_factor_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (ι → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_pi_of_isLocallyConstant hf
  refine ⟨U, fun q => f fun i => (q i).out, funext fun x => hU _ _ fun i => ?_⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (x i : G ⧸ (U : Subgroup G))).symm

theorem exists_openNormalSubgroup_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : Fin n → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y :=
  exists_openNormalSubgroup_pi_of_isLocallyConstant hf

theorem exists_openNormalSubgroup_factor_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (Fin n → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) :=
  exists_openNormalSubgroup_factor_of_isLocallyConstant hf

end Factor

end Langlands.ProfiniteCohomology
