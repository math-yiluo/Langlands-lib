import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Compact

/-! # Separating a point of a finite fibre by a relatively clopen neighborhood -/

universe u v w

namespace Langlands.Analytic

open Set Filter
open scoped Topology

variable {Y : Type u} {X : Type v} [TopologicalSpace Y] [TopologicalSpace X]

/-- `O` is a relatively clopen part of `Y'` over `𝒰`: both are open, `O` lies
in `Y'`, `𝒰` contains `x`, and inside `Y' ∩ f⁻¹(𝒰)` the closure of `O` adds no
point. -/
def IsClopenOver (f : Y → X) (Y' : Set Y) (x : X) (O : Set Y) (𝒰 : Set X) : Prop :=
  IsOpen O ∧ O ⊆ Y' ∧ IsOpen 𝒰 ∧ x ∈ 𝒰 ∧ Y' ∩ f ⁻¹' 𝒰 ∩ closure O ⊆ O

/-- Inside a Hausdorff subset, a compact set is the trace of a closed set. -/
theorem exists_isClosed_inter_eq_of_isCompact {H : Set X} [T2Space H] {K : Set X}
    (hK : IsCompact K) (hKH : K ⊆ H) : ∃ t : Set X, IsClosed t ∧ t ∩ H = K := by
  have hc : IsCompact (Subtype.val ⁻¹' K : Set H) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hKH]
    exact hK
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.1 hc.isClosed
  refine ⟨t, ht, Set.ext fun z => ⟨fun ⟨hzt, hzH⟩ => ?_, fun hz => ⟨?_, hKH hz⟩⟩⟩
  · have : (⟨z, hzH⟩ : H) ∈ Subtype.val ⁻¹' t := hzt
    rw [hteq] at this
    exact this
  · have : (⟨z, hKH hz⟩ : H) ∈ Subtype.val ⁻¹' K := hz
    rw [← hteq] at this
    exact this

/-- Separation of a point of a finite fibre. Let `f` be continuous, `Y'` open,
and let finitely many compact sets `W k`, all containing `x` and lying in a
Hausdorff subset `H`, have union a neighborhood of `x`. Suppose each
`Y' ∩ f⁻¹(W k)` is compact and Hausdorff and the fibre `Y' ∩ f⁻¹{x}` is finite.
Then every fibre point `y` has an open neighborhood `O` inside any prescribed
neighborhood, together with an open neighborhood `𝒰` of `x` inside the union,
such that `O` is relatively clopen in `Y' ∩ f⁻¹(𝒰)`. -/
theorem exists_isClopenOver_of_finite_fibre {f : Y → X} (hf : Continuous f) {Y' : Set Y}
    (hY' : IsOpen Y') {x : X} {H : Set X} [T2Space H] {ι : Type w} [Finite ι]
    (W : ι → Set X) (hWc : ∀ k, IsCompact (W k)) (hWH : ∀ k, W k ⊆ H)
    (hxW : ∀ k, x ∈ W k) (hN : (⋃ k, W k) ∈ 𝓝 x)
    (hPc : ∀ k, IsCompact (Y' ∩ f ⁻¹' W k)) (hPt : ∀ k, T2Space (Y' ∩ f ⁻¹' W k : Set Y))
    (hF : (Y' ∩ f ⁻¹' {x}).Finite) {y : Y} (hy : y ∈ Y') (hyx : f y = x)
    {V₀ : Set Y} (hV₀ : V₀ ∈ 𝓝 y) :
    ∃ O 𝒰, IsClopenOver f Y' x O 𝒰 ∧ y ∈ O ∧ O ⊆ V₀ ∧ 𝒰 ⊆ ⋃ k, W k := by
  classical
  choose t ht htW using fun k => exists_isClosed_inter_eq_of_isCompact (hWc k) (hWH k)
  have hWt : ∀ k, W k ⊆ t k := fun k z hz => ((htW k).symm ▸ hz : z ∈ t k ∩ H).1
  have hNH : (⋃ k, W k) ⊆ H := Set.iUnion_subset hWH
  let N₀ := interior (⋃ k, W k)
  have hxN₀ : x ∈ N₀ := mem_interior_iff_mem_nhds.2 hN
  have hN₀H : N₀ ⊆ H := interior_subset.trans hNH
  let P : ι → Set Y := fun k => Y' ∩ f ⁻¹' W k
  let F : Set Y := Y' ∩ f ⁻¹' {x}
  have hyP : ∀ k, y ∈ P k := fun k => ⟨hy, show f y ∈ W k from hyx ▸ hxW k⟩
  -- A separating neighborhood of `y` inside each compact Hausdorff piece.
  have key : ∀ k, ∃ G C : Set Y, IsOpen G ∧ y ∈ G ∧ G ∩ P k ⊆ V₀ ∧ IsCompact C ∧
      C ⊆ P k ∧ (∀ p ∈ C, p ∈ F → p = y) ∧ closure (G ∩ P k) ∩ P k ⊆ C := by
    intro k
    have : CompactSpace (P k) := isCompact_iff_compactSpace.mp (hPc k)
    have : T2Space (P k) := hPt k
    let y' : P k := ⟨y, hyP k⟩
    let F' : Set (P k) := {q | q.1 ∈ F ∧ q.1 ≠ y}
    have hF'fin : F'.Finite :=
      (hF.preimage Subtype.val_injective.injOn).subset fun q hq => hq.1
    have hF'closed : IsClosed F' := hF'fin.isClosed
    have hy'F' : y' ∉ F' := fun h => h.2 rfl
    have hnhds : F'ᶜ ∩ Subtype.val ⁻¹' V₀ ∈ 𝓝 y' :=
      Filter.inter_mem (hF'closed.isOpen_compl.mem_nhds hy'F')
        (continuous_subtype_val.continuousAt.preimage_mem_nhds hV₀)
    obtain ⟨D, ⟨hDN, hDc⟩, hDsub⟩ := (closed_nhds_basis y').mem_iff.1 hnhds
    obtain ⟨G, hG, hGS⟩ := isOpen_induced_iff.1 (isOpen_interior : IsOpen (interior D))
    have hGP : G ∩ P k = Subtype.val '' interior D := by
      ext p
      constructor
      · rintro ⟨hpG, hpP⟩
        exact ⟨⟨p, hpP⟩, hGS ▸ hpG, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨(hGS.symm ▸ hq : q ∈ Subtype.val ⁻¹' G), q.2⟩
    refine ⟨G, Subtype.val '' closure (interior D), hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : y' ∈ interior D := mem_interior_iff_mem_nhds.2 hDN
      have h2 : y' ∈ Subtype.val ⁻¹' G := hGS.symm ▸ this
      exact h2
    · rw [hGP]
      rintro _ ⟨q, hq, rfl⟩
      exact (hDsub (interior_subset hq)).2
    · exact isClosed_closure.isCompact.image continuous_subtype_val
    · rintro _ ⟨q, -, rfl⟩
      exact q.2
    · rintro _ ⟨q, hq, rfl⟩ hqF
      have hqD : q ∈ D := (closure_minimal interior_subset hDc) hq
      by_contra hne
      exact (hDsub hqD).1 ⟨hqF, hne⟩
    · rintro p ⟨hpcl, hpP⟩
      refine ⟨⟨p, hpP⟩, ?_, rfl⟩
      rw [closure_subtype]
      rw [hGP] at hpcl
      exact hpcl
  choose G C hG hyG hGV hCc hCP hCF hcl using key
  let O : Set Y := (Y' ∩ f ⁻¹' N₀) ∩ ⋂ k, ((f ⁻¹' t k)ᶜ ∪ G k)
  have hOopen : IsOpen O :=
    (hY'.inter (isOpen_interior.preimage hf)).inter
      (isOpen_iInter_of_finite fun k => ((ht k).preimage hf).isOpen_compl.union (hG k))
  have hmemP : ∀ p, p ∈ Y' → f p ∈ N₀ → ∀ k, f p ∈ t k → p ∈ P k := fun p hp hpN k hpt =>
    ⟨hp, show f p ∈ W k from htW k ▸ ⟨hpt, hN₀H hpN⟩⟩
  have hOsub : O ⊆ ⋃ k, G k ∩ P k := by
    rintro p ⟨⟨hpY, hpN⟩, hpI⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (interior_subset hpN : f p ∈ ⋃ k, W k)
    refine Set.mem_iUnion.2 ⟨k, ?_, hpY, hk⟩
    rcases Set.mem_iInter.1 hpI k with h | h
    · exact absurd (hWt k hk) h
    · exact h
  have hyO : y ∈ O := ⟨⟨hy, show f y ∈ N₀ from hyx ▸ hxN₀⟩,
    Set.mem_iInter.2 fun k => Or.inr (hyG k)⟩
  have hclosure : ∀ p ∈ closure O, f p ∈ N₀ → p ∈ Y' → ∃ k, p ∈ C k := by
    intro p hpO hpN hpY
    have h1 : p ∈ closure (⋃ k, G k ∩ P k) := closure_mono hOsub hpO
    rw [closure_iUnion_of_finite] at h1
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h1
    have hpt : f p ∈ t k := by
      have hsub : G k ∩ P k ⊆ f ⁻¹' t k := fun q hq => hWt k hq.2.2
      exact closure_minimal hsub ((ht k).preimage hf) hk
    exact ⟨k, hcl k ⟨hk, hmemP p hpY hpN k hpt⟩⟩
  let Z : Set X := ⋃ k, f '' (C k \ O)
  have hZc : IsCompact Z := isCompact_iUnion fun k => ((hCc k).diff hOopen).image hf
  have hZH : Z ⊆ H := Set.iUnion_subset fun k => by
    rintro _ ⟨p, hp, rfl⟩
    exact hWH k (hCP k hp.1).2
  have hxZ : x ∉ Z := by
    intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, ⟨hpC, hpO⟩, hpx⟩ := hk
    have hpF : p ∈ F := ⟨(hCP k hpC).1, hpx⟩
    exact hpO (hCF k p hpC hpF ▸ hyO)
  obtain ⟨T, hT, hTZ⟩ := exists_isClosed_inter_eq_of_isCompact hZc hZH
  refine ⟨O, N₀ ∩ Tᶜ, ⟨hOopen, fun p hp => hp.1.1, isOpen_interior.inter hT.isOpen_compl,
    ⟨hxN₀, fun hxT => hxZ (hTZ ▸ ⟨hxT, hN₀H hxN₀⟩)⟩, ?_⟩, hyO, ?_,
    fun z hz => interior_subset hz.1⟩
  · rintro p ⟨⟨hpY, hpN, hpT⟩, hpO⟩
    obtain ⟨k, hk⟩ := hclosure p hpO hpN hpY
    by_contra hpO'
    have hZ : f p ∈ Z := Set.mem_iUnion.2 ⟨k, p, ⟨hk, hpO'⟩, rfl⟩
    have hTH : f p ∈ T ∩ H := hTZ.symm ▸ hZ
    exact hpT hTH.1
  · intro p hp
    obtain ⟨k, hkG, hkP⟩ := Set.mem_iUnion.1 (hOsub hp)
    exact hGV k ⟨hkG, hkP⟩

end Langlands.Analytic
