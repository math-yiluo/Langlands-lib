import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Group

/-! # A compactness argument for supports near a point

Let `G` be a locally compact Hausdorff topological group, `θ` a continuous map of `G`, `K ⊆ G`
compact, `P` a closed subgroup, `pr` a continuous map on `P` and `V` an open set in its target.
If, for every `k ∈ K` with `k δ θ(k)⁻¹ ∈ P`, the projection of `k δ θ(k)⁻¹` lies in `V`, then
there is an open neighbourhood `U₀` of `δ` such that `pr(p) ∈ V` whenever `p ∈ P`, `k ∈ K` and
`k⁻¹ p θ(k) ∈ U₀`. See the paired Markdown.
-/

namespace Langlands.BaseChange.TwistedLocalDescent

open Set

universe u v

/-- **Support lemma.** -/
theorem exists_nhds_forall_proj_mem {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] (θ : G → G) (hθ : Continuous θ)
    {K : Set G} (hK : IsCompact K) (P : Subgroup G) (hP : IsClosed (P : Set G))
    {M : Type v} [TopologicalSpace M] (pr : P → M) (hpr : Continuous pr) {V : Set M}
    (hV : IsOpen V) (δ : G)
    (h : ∀ k ∈ K, ∀ hp : k * δ * (θ k)⁻¹ ∈ P, pr ⟨_, hp⟩ ∈ V) :
    ∃ U₀ : Set G, IsOpen U₀ ∧ δ ∈ U₀ ∧
      ∀ k ∈ K, ∀ p : P, k⁻¹ * (p : G) * θ k ∈ U₀ → pr p ∈ V := by
  obtain ⟨U₁, hU₁c, hU₁n⟩ := exists_compact_mem_nhds δ
  let Z : Set G := Subtype.val '' (pr ⁻¹' Vᶜ)
  have hZ : IsClosed Z :=
    hP.isClosedEmbedding_subtypeVal.isClosedMap _ (hV.isClosed_compl.preimage hpr)
  let f : G × G → G := fun ky => ky.1 * ky.2 * (θ ky.1)⁻¹
  have hf : Continuous f :=
    (continuous_fst.mul continuous_snd).mul (hθ.comp continuous_fst).inv
  let T : Set (G × G) := (K ×ˢ U₁) ∩ f ⁻¹' Z
  have hT : IsCompact T := (hK.prod hU₁c).inter_right (hZ.preimage hf)
  have hTs : IsClosed (Prod.snd '' T) := (hT.image continuous_snd).isClosed
  have hδT : δ ∉ Prod.snd '' T := by
    rintro ⟨⟨k, y⟩, ⟨⟨hk, -⟩, hfZ⟩, rfl⟩
    obtain ⟨p, hpV, hp⟩ := hfZ
    have hpP : k * y * (θ k)⁻¹ ∈ P := by
      have := p.property
      rwa [hp] at this
    apply hpV
    have := h k hk hpP
    have hpeq : p = ⟨_, hpP⟩ := Subtype.ext hp
    rw [hpeq]
    exact this
  refine ⟨interior U₁ ∩ (Prod.snd '' T)ᶜ, isOpen_interior.inter hTs.isOpen_compl,
    ⟨mem_interior_iff_mem_nhds.mpr hU₁n, hδT⟩, ?_⟩
  intro k hk p hy
  by_contra hpV
  apply hy.2
  refine ⟨(k, k⁻¹ * (p : G) * θ k), ⟨⟨hk, interior_subset hy.1⟩, ?_⟩, rfl⟩
  refine ⟨p, hpV, ?_⟩
  change (p : G) = k * (k⁻¹ * (p : G) * θ k) * (θ k)⁻¹
  group

end Langlands.BaseChange.TwistedLocalDescent
