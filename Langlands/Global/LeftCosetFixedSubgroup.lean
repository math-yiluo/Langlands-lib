import Langlands.Global.LeftCosetSpace
import Mathlib.Topology.Sequences
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Closed quotient embeddings for fixed subgroups -/

noncomputable section

universe u v

open Topology Filter

namespace Langlands.Global.LeftCosetSpace

variable {G : Type u} [Group G] (Γ H : Subgroup G)

/-- The natural map from the quotient of a subgroup into the ambient quotient. -/
def subgroupInclusion : LeftCosetSpace (Γ.subgroupOf H) → LeftCosetSpace Γ :=
  Quotient.map' (fun x : H => (x : G)) (by
    intro x y h
    apply QuotientGroup.rightRel_apply.mpr
    have hh : y * x⁻¹ ∈ Γ.subgroupOf H := QuotientGroup.rightRel_apply.mp h
    exact hh)

@[simp] theorem subgroupInclusion_mk (x : H) :
    subgroupInclusion Γ H (mk (Γ.subgroupOf H) x) = mk Γ (x : G) := rfl

theorem subgroupInclusion_injective : Function.Injective (subgroupInclusion Γ H) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  apply (mk_eq_mk_iff (Γ.subgroupOf H) x y).mpr
  exact (mk_eq_mk_iff Γ (x : G) (y : G)).mp h

variable [TopologicalSpace G]

theorem continuous_subgroupInclusion : Continuous (subgroupInclusion Γ H) := by
  apply (continuous_iff (Γ.subgroupOf H)).mpr
  exact (continuous_mk Γ).comp continuous_subtype_val

section Fixed

variable [IsTopologicalGroup G] [T2Space G] [SequentialSpace G] [DiscreteTopology Γ]
  {I : Type v} [Finite I] (f : I → G →ₜ* G)
  (hΓ : IsClosed (Γ : Set G))
  (hfΓ : ∀ i, ∀ γ ∈ Γ, f i γ ∈ Γ)
  (hH : ∀ x : G, x ∈ H ↔ ∀ i, f i x = x)

include hH

omit [IsTopologicalGroup G] [SequentialSpace G] [Finite I] in
/-- The common fixed subgroup is closed in the original topological group. -/
theorem isClosed_fixedSubgroup : IsClosed (H : Set G) := by
  have he : (H : Set G) = ⋂ i, {x : G | f i x = x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact hH x
  rw [he]
  exact isClosed_iInter fun i => isClosed_eq (f i).continuous continuous_id

include hΓ hfΓ hH

omit [T2Space G] in
/-- A closed set in the fixed subgroup, invariant under its discrete subgroup,
has closed saturation by the ambient discrete subgroup. -/
theorem isClosed_saturation_fixed {E : Set G} (hE : IsClosed E)
    (hEH : E ⊆ H)
    (hEinv : ∀ γ : Γ, (γ : G) ∈ H → ∀ e ∈ E, (γ : G) * e ∈ E) :
    IsClosed (⋃ γ : Γ, (fun e : G => (γ : G) * e) '' E) := by
  classical
  apply IsSeqClosed.isClosed
  intro z x hz hzx
  have hex (n : ℕ) : ∃ γ : Γ, ∃ e ∈ E, (γ : G) * e = z n :=
    Set.mem_iUnion.mp (hz n)
  choose γ e he hze using hex
  have hcoc (n : ℕ) (i : I) : z n * (f i (z n))⁻¹ =
      (γ n : G) * (f i (γ n : G))⁻¹ := by
    rw [← hze n, map_mul, (hH _).mp (hEH (he n)) i]
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have hcmem (n : ℕ) (i : I) : z n * (f i (z n))⁻¹ ∈ Γ := by
    rw [hcoc]
    exact Γ.mul_mem (γ n).property (Γ.inv_mem (hfΓ i _ (γ n).property))
  have hev (i : I) : ∀ᶠ n in atTop,
      z n * (f i (z n))⁻¹ = x * (f i x)⁻¹ := by
    have ht : Tendsto (fun n => z n * (f i (z n))⁻¹) atTop (𝓝 (x * (f i x)⁻¹)) :=
      hzx.mul (((f i).continuous.tendsto x).comp hzx).inv
    have hx : x * (f i x)⁻¹ ∈ Γ := hΓ.mem_of_tendsto ht (Eventually.of_forall fun n => hcmem n i)
    let w : ℕ → Γ := fun n => ⟨z n * (f i (z n))⁻¹, hcmem n i⟩
    have htw : Tendsto w atTop (𝓝 (⟨x * (f i x)⁻¹, hx⟩ : Γ)) :=
      tendsto_subtype_rng.mpr ht
    have hw : ∀ᶠ n in atTop, w n = (⟨x * (f i x)⁻¹, hx⟩ : Γ) := by
      simpa only [nhds_discrete, tendsto_pure] using htw
    filter_upwards [hw] with n hn
    exact congrArg Subtype.val hn
  obtain ⟨N, hN⟩ := (eventually_all.mpr hev).exists_forall_of_atTop
  have hfixed (n : ℕ) (hn : N ≤ n) : (γ N : G)⁻¹ * (γ n : G) ∈ H := by
    apply (hH _).mpr
    intro i
    have hh : (γ n : G) * (f i (γ n : G))⁻¹ =
        (γ N : G) * (f i (γ N : G))⁻¹ := by
      rw [← hcoc n i, ← hcoc N i, hN n hn i, hN N le_rfl i]
    have hd := congrArg (fun a : G => (γ N : G)⁻¹ * a)
      (mul_inv_eq_iff_eq_mul.mp hh)
    rw [map_mul, map_inv]
    symm
    simpa only [mul_assoc, inv_mul_cancel_left] using hd
  have hEv : ∀ᶠ n in atTop, (γ N : G)⁻¹ * z n ∈ E := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hm := hEinv ⟨(γ N : G)⁻¹ * (γ n : G),
      Γ.mul_mem (Γ.inv_mem (γ N).property) (γ n).property⟩ (hfixed n hn) (e n) (he n)
    simpa only [hze, mul_assoc] using hm
  have hxE := hE.mem_of_tendsto (tendsto_const_nhds.mul hzx) hEv
  exact Set.mem_iUnion.mpr ⟨γ N, (γ N : G)⁻¹ * x, hxE, mul_inv_cancel_left _ _⟩

/-- The fixed-subgroup quotient embeds as a closed subspace of the ambient quotient. -/
theorem isClosedEmbedding_subgroupInclusion_fixed :
    IsClosedEmbedding (subgroupInclusion Γ H) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_subgroupInclusion Γ H) (subgroupInclusion_injective Γ H)
  intro C hC
  let E : Set G := (fun x : H => (x : G)) '' (mk (Γ.subgroupOf H) ⁻¹' C)
  have hE : IsClosed E :=
    (isClosed_fixedSubgroup H f hH).isClosedMap_subtype_val _
      (hC.preimage (continuous_mk (Γ.subgroupOf H)))
  have hEH : E ⊆ H := by
    rintro _ ⟨e, _, rfl⟩
    exact e.property
  have hEinv : ∀ γ : Γ, (γ : G) ∈ H → ∀ e ∈ E, (γ : G) * e ∈ E := by
    rintro γ hγ _ ⟨e, he, rfl⟩
    refine ⟨(⟨γ, hγ⟩ : H) * e, ?_, rfl⟩
    change mk (Γ.subgroupOf H) ((⟨γ, hγ⟩ : H) * e) ∈ C
    rw [mk_subgroup_mul (Γ.subgroupOf H) ⟨⟨γ, hγ⟩, γ.property⟩ e]
    exact he
  have hs := isClosed_saturation_fixed Γ H f hΓ hfΓ hH hE hEH hEinv
  apply (isQuotientMap_mk Γ).isCoinducing.isClosed_preimage.mp
  have hpre : mk Γ ⁻¹' (subgroupInclusion Γ H '' C) =
      ⋃ γ : Γ, (fun e : G => (γ : G) * e) '' E := by
    ext x
    constructor
    · rintro ⟨q, hq, hqx⟩
      obtain ⟨e, rfl⟩ := mk_surjective (Γ.subgroupOf H) q
      have hγ : x * (e : G)⁻¹ ∈ Γ := (mk_eq_mk_iff Γ _ _).mp hqx
      refine Set.mem_iUnion.mpr ⟨⟨x * (e : G)⁻¹, hγ⟩, e, ⟨e, hq, rfl⟩, ?_⟩
      exact inv_mul_cancel_right _ _
    · rintro hx
      obtain ⟨γ, e, he, rfl⟩ := Set.mem_iUnion.mp hx
      obtain ⟨e, he, rfl⟩ := he
      exact ⟨mk (Γ.subgroupOf H) e, he, (mk_subgroup_mul Γ γ e).symm⟩
  rw [hpre]
  exact hs

end Fixed
end Langlands.Global.LeftCosetSpace
