import Langlands.Representation.Smooth.CompactCompletionAction
import Langlands.Representation.Smooth.CompactCompletionCofinal
import Mathlib.Topology.Compactness.Compact

/-!
# Fixed completion families and cofinal fixed components

Compact subgroups normalize arbitrarily small compact open subgroups. This
allows fixed completion families to be detected on cofinal sets of components.
The final comparison isolates the two stable-image consequences used in the
proof of Renard VI.9.7.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz.CompactOpenSubgroup

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def compactCoreSubgroup (K : CompactOpenSubgroup G) (C : Subgroup G) :
    Subgroup G where
  carrier := {x | ∀ c : C, (c : G) * x * (c : G)⁻¹ ∈ K.1}
  one_mem' := by
    intro c
    simp
  mul_mem' := by
    intro x y hx hy c
    simpa [mul_assoc] using K.1.mul_mem (hx c) (hy c)
  inv_mem' := by
    intro x hx c
    simpa [mul_assoc] using K.1.inv_mem (hx c)

omit [IsTopologicalGroup G] in
private theorem compactCoreSubgroup_le (K : CompactOpenSubgroup G) (C : Subgroup G) :
    compactCoreSubgroup K C ≤ K.1.toSubgroup := by
  intro x hx
  simpa using hx (1 : C)

private theorem compactCoreSubgroup_isOpen (K : CompactOpenSubgroup G)
    (C : Subgroup G) (hC : IsCompact (C : Set G)) :
    IsOpen (compactCoreSubgroup K C : Set G) := by
  have hopen : IsOpen {p : G × G | p.1 * p.2 * p.1⁻¹ ∈ K.1} :=
    K.1.isOpen.preimage ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hprod : (C : Set G) ×ˢ ({1} : Set G) ⊆
      {p : G × G | p.1 * p.2 * p.1⁻¹ ∈ K.1} := by
    rintro ⟨c, x⟩ ⟨_, rfl⟩
    simp
  obtain ⟨U, W, _, hW, hCU, h1W, hUW⟩ :=
    generalized_tube_lemma hC isCompact_singleton hopen hprod
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hW.mem_nhds (h1W (Set.mem_singleton 1))) ?_
  intro x hx c
  exact hUW (a := ((c : G), x)) ⟨hCU c.property, hx⟩

/-- Every compact open subgroup contains one normalized by a given compact
subgroup. No local compactness or nonarchimedean hypothesis is needed. -/
theorem exists_le_normalizedBy_compact (K : CompactOpenSubgroup G)
    (C : Subgroup G) (hC : IsCompact (C : Set G)) :
    ∃ L : CompactOpenSubgroup G, L.1 ≤ K.1 ∧ ∀ c ∈ C, L.conj c = L := by
  let H : OpenSubgroup G :=
    ⟨compactCoreSubgroup K C, compactCoreSubgroup_isOpen K C hC⟩
  let L : CompactOpenSubgroup G :=
    ⟨H, K.2.of_isClosed_subset H.isClosed (compactCoreSubgroup_le K C)⟩
  refine ⟨L, compactCoreSubgroup_le K C, ?_⟩
  intro c hc
  apply Subtype.ext
  ext x
  rw [mem_conj]
  change (∀ a : C, (a : G) * (c⁻¹ * x * c) * (a : G)⁻¹ ∈ K.1) ↔
    ∀ a : C, (a : G) * x * (a : G)⁻¹ ∈ K.1
  constructor
  · intro hx a
    have ha := hx ⟨(a : G) * c, C.mul_mem a.property hc⟩
    simpa [mul_assoc] using ha
  · intro hx a
    have ha := hx ⟨(a : G) * c⁻¹, C.mul_mem a.property (C.inv_mem hc)⟩
    simpa [mul_assoc] using ha

end Langlands.HarishChandraSchwartz.CompactOpenSubgroup

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- A component whose index is normalized by `c` is fixed by `c` whenever the
completion family is fixed by `c`. -/
theorem component_fixed_of_conj_eq (v : completion ρ hρ) (c : G)
    (hv : translate ρ c v.1 = v.1) (K : CompactOpenSubgroup G)
    (hK : K.conj c⁻¹ = K) :
    ρ c (v.1 K) = v.1 K := by
  have heq := congrFun hv K
  simpa only [translate, hK] using heq

/-- A compact-subgroup-fixed completion family has fixed components on a
cofinal set of compact open subgroups. -/
theorem cofinal_fixed_components_of_fixed (C : Subgroup G) (hC : IsCompact (C : Set G))
    (v : completion ρ hρ) (hv : v ∈ completionFixed ρ hρ C) :
    IsCofinal {K : CompactOpenSubgroup G | v.1 K ∈ fixedVectors ρ C} := by
  intro K
  obtain ⟨L, hLK, hLC⟩ := K.exists_le_normalizedBy_compact C hC
  refine ⟨L, ?_, hLK⟩
  intro c
  exact component_fixed_of_conj_eq ρ hρ v c (hv c c.property) L
    (hLC c⁻¹ (C.inv_mem c.property))

/-- If cofinally many components are fixed by `c`, then the whole completion
family is fixed by `c`. The comparison uses an index below both `K` and
`c⁻¹ K c`. -/
theorem translate_eq_of_cofinally_fixed (v : completion ρ hρ) (c : G)
    (hv : IsCofinal {K : CompactOpenSubgroup G | ρ c (v.1 K) = v.1 K}) :
    translate ρ c v.1 = v.1 := by
  funext K
  obtain ⟨L, hL, hLK⟩ := hv (K.inf (K.conj c⁻¹))
  have hLK₁ : L.1 ≤ K.1 := hLK.trans inf_le_left
  have hLK₂ : L.1 ≤ (K.conj c⁻¹).1 := hLK.trans inf_le_right
  change ρ c (v.1 (K.conj c⁻¹)) = v.1 K
  rw [← v.property _ L hLK₂, ← averageMap_translate, hL, v.property _ L hLK₁]

/-- For a subgroup covered by compact subgroups, completion fixedness is
equivalent to cofinal fixedness of components for each compact subgroup. -/
theorem mem_completionFixed_iff_cofinal_fixed_components (H : Subgroup G)
    (hH : ∀ h ∈ H, ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ H ∧ h ∈ C)
    (v : completion ρ hρ) :
    v ∈ completionFixed ρ hρ H ↔
      ∀ C : Subgroup G, IsCompact (C : Set G) → C ≤ H →
        IsCofinal {K : CompactOpenSubgroup G | v.1 K ∈ fixedVectors ρ C} := by
  constructor
  · intro hv C hC hCH
    exact cofinal_fixed_components_of_fixed ρ hρ C hC v
      (fun c hc => hv c (hCH hc))
  · intro hv h hh
    obtain ⟨C, hC, hCH, hhC⟩ := hH h hh
    apply translate_eq_of_cofinally_fixed ρ hρ v h
    intro K
    obtain ⟨L, hL, hLK⟩ := hv C hC hCH K
    exact ⟨L, hL ⟨h, hhC⟩, hLK⟩

/-- Completion families whose components in `S` lie in prescribed subspaces. -/
def componentsIn (S : Set (CompactOpenSubgroup G))
    (W : CompactOpenSubgroup G → Submodule ℂ V) : Submodule ℂ (completion ρ hρ) where
  carrier := {v | ∀ K ∈ S, v.1 K ∈ W K}
  zero_mem' := by
    intro K _
    exact (W K).zero_mem
  add_mem' := by
    intro v w hv hw K hK
    exact (W K).add_mem (hv K hK) (hw K hK)
  smul_mem' := by
    intro c v hv K hK
    exact (W K).smul_mem c (hv K hK)

/-- The fixed-completion comparison in VI.9.7, with its two structural inputs
explicit. The first input places averaged compact-fixed vectors in `W K`. The
second supplies a cofinal set of indices on which `W K` is compact-fixed.
For the application, `W K` is the stable image in `V` and both inputs come from
the second Remark of VI.9.1. -/
theorem componentsIn_eq_completionFixed (H : Subgroup G)
    (hH : ∀ h ∈ H, ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ H ∧ h ∈ C)
    (S : Set (CompactOpenSubgroup G))
    (W : CompactOpenSubgroup G → Submodule ℂ V)
    (haverage : ∀ K ∈ S, ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ H ∧
      (fixedVectors ρ C).map (Compact.averageMap ρ hρ K.1 K.2) ≤ W K)
    (hfixed : ∀ C : Subgroup G, IsCompact (C : Set G) → C ≤ H →
      IsCofinal {K : CompactOpenSubgroup G | K ∈ S ∧ W K ≤ fixedVectors ρ C}) :
    componentsIn ρ hρ S W = completionFixed ρ hρ H := by
  ext v
  constructor
  · intro hv
    apply (mem_completionFixed_iff_cofinal_fixed_components ρ hρ H hH v).mpr
    intro C hC hCH K
    obtain ⟨L, ⟨hLS, hLW⟩, hLK⟩ := hfixed C hC hCH K
    exact ⟨L, hLW (hv L hLS), hLK⟩
  · intro hv K hKS
    obtain ⟨C, hC, hCH, hCW⟩ := haverage K hKS
    have hcof := cofinal_fixed_components_of_fixed ρ hρ C hC v
      (fun c hc => hv c (hCH hc))
    obtain ⟨L, hLC, hLK⟩ := hcof K
    exact hCW ⟨v.1 L, hLC, v.property K L hLK⟩

end Langlands.CompactCompletion
