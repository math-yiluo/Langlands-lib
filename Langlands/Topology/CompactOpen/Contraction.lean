import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact

/-! # Compact-open containment from a continuous contraction family -/

noncomputable section

universe u v

open Set Filter Topology

namespace Langlands

/-- A continuous family that is constant at the identity at an accumulation
parameter, and is a topological group automorphism at every other parameter,
transports any fixed compact open subgroup to one containing a given compact set. -/
theorem compactOpenContainment_of_contractingFamily
    {T : Type v} [TopologicalSpace T] (t₀ : T)
    [NeBot (𝓝[≠] t₀)]
    {H : Type u} [Group H] [TopologicalSpace H]
    (f : T × H → H) (hf : Continuous f)
    (hzero : ∀ x, f (t₀, x) = 1)
    (haut : ∀ t, t ≠ t₀ → ∃ e : H ≃ₜ* H, ∀ x, f (t, x) = e x)
    (K₀ : OpenSubgroup H) (hK₀ : IsCompact (K₀ : Set H))
    (C : Set H) (hC : IsCompact C) :
    ∃ K : OpenSubgroup H, IsCompact (K : Set H) ∧ C ⊆ (K : Set H) := by
  have hprod : ({t₀} : Set T) ×ˢ C ⊆ f ⁻¹' (K₀ : Set H) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht' : t = t₀ := ht
    subst t
    change f (t₀, x) ∈ K₀
    rw [hzero]
    exact K₀.one_mem
  obtain ⟨V, W, hV, _, htV, hCW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hC (K₀.isOpen.preimage hf) hprod
  obtain ⟨t, ht, htne⟩ :=
    nhdsWithin_neBot.mp (inferInstance : NeBot (𝓝[≠] t₀))
      (hV.mem_nhds (htV (mem_singleton t₀)))
  have htne' : t ≠ t₀ := by simpa using htne
  obtain ⟨e, he⟩ := haut t htne'
  refine ⟨K₀.comap e.toMonoidHom e.continuous, ?_, ?_⟩
  · change IsCompact (e.toHomeomorph ⁻¹' (K₀ : Set H))
    rw [← e.toHomeomorph.image_symm]
    exact hK₀.image e.symm.continuous
  · intro x hx
    change e x ∈ K₀
    rw [← he x]
    exact hVW ⟨ht, hCW hx⟩

/-- A compact open subgroup containing `C`, selected from the contraction argument. -/
def compactOpenContainingOfContractingFamily
    {T : Type v} [TopologicalSpace T] (t₀ : T)
    [NeBot (𝓝[≠] t₀)]
    {H : Type u} [Group H] [TopologicalSpace H]
    (f : T × H → H) (hf : Continuous f)
    (hzero : ∀ x, f (t₀, x) = 1)
    (haut : ∀ t, t ≠ t₀ → ∃ e : H ≃ₜ* H, ∀ x, f (t, x) = e x)
    (K₀ : OpenSubgroup H) (hK₀ : IsCompact (K₀ : Set H))
    (C : Set H) (hC : IsCompact C) :
    {K : OpenSubgroup H // IsCompact (K : Set H) ∧ C ⊆ (K : Set H)} :=
  ⟨(compactOpenContainment_of_contractingFamily t₀ f hf hzero haut K₀ hK₀ C hC).choose,
    (compactOpenContainment_of_contractingFamily t₀ f hf hzero haut K₀ hK₀ C hC).choose_spec⟩

end Langlands
