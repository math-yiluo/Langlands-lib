import Langlands.Representation.Jacquet.StableImageAveraging
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Langlands.Representation.Smooth.CompactCompletionFixed

/-!
# Stable-image families and the fixed completion

Compact exhaustion for the opposite contraction and averaging through compact
cores identify stationary stable-image families with the lower-fixed completion.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exhaustion by conjugates of an open subgroup is uniform on compact subsets
of the contracting subgroup. -/
theorem IsIwahoriContraction.exists_uniform_exhaust
    {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (C : Set G) (hC : IsCompact C) (hCN : C ⊆ N) :
    ∃ b : ℕ, ∀ x ∈ C, g ^ b * x * (g ^ b)⁻¹ ∈ K := by
  let U : ℕ → Set G := fun b => {x | g ^ b * x * (g ^ b)⁻¹ ∈ K}
  have hopen : ∀ b, IsOpen (U b) := fun b =>
    K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hcover : C ⊆ ⋃ b, U b := by
    intro x hx
    obtain ⟨b, hb⟩ := h.exhaust x (hCN hx)
    exact Set.mem_iUnion.mpr ⟨b, hb⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hopen hcover
  refine ⟨t.sup id, fun x hx => ?_⟩
  obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hbxN : g ^ b * x * (g ^ b)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (pow_mem (hMN h.mem_levi) b) x).mp (hCN hx)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := id) hbt)
  rw [hs]
  change g ^ (b + s) * x * (g ^ (b + s))⁻¹ ∈ K
  have heq : g ^ (b + s) * x * (g ^ (b + s))⁻¹ =
      g ^ s * (g ^ b * x * (g ^ b)⁻¹) * (g ^ s)⁻¹ := by group
  rw [heq]
  exact (h.upper_pow s _ ⟨hxb, hbxN⟩).1

/-- Every compact part of the lower group is contained in one expanded lower
factor when the opposite Iwahori contraction is available. -/
theorem exists_le_expandedLowerSubgroup_of_opposite
    {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}
    (h : IsIwahoriContraction K Nbar M N g⁻¹)
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (C : Subgroup G) (hC : IsCompact (C : Set G)) (hCNbar : C ≤ Nbar) :
    ∃ b : ℕ, C ≤ expandedLowerSubgroup K Nbar g b := by
  obtain ⟨b, hb⟩ := h.exists_uniform_exhaust hMNbar (C : Set G) hC hCNbar
  refine ⟨b, fun x hx => ?_⟩
  have hxK : (g ^ b)⁻¹ * x * g ^ b ∈ K := by
    simpa only [inv_pow, inv_inv] using hb x hx
  have hxNbar : (g ^ b)⁻¹ * x * g ^ b ∈ Nbar :=
    by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (inv_mem (pow_mem (hMNbar (by simpa using M.inv_mem h.mem_levi)) b)) x).mp
        (hCNbar hx)
  refine ⟨(g ^ b)⁻¹ * x * g ^ b, ⟨hxK, hxNbar⟩, ?_⟩
  change g ^ b * ((g ^ b)⁻¹ * x * g ^ b) * (g ^ b)⁻¹ = x
  group

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The stable image is contained in the average of the vectors fixed by every
given compact lower subgroup. Stationarity is not required for this inclusion. -/
theorem stableImage_le_average_compact_fixed
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
    {N M Nbar : Subgroup G} {g : G}
    (h : IsIwahoriContraction K N M Nbar g)
    (hopp : IsIwahoriContraction K Nbar M N g⁻¹)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (C : Subgroup G) (hC : IsCompact (C : Set G)) (hCNbar : C ≤ Nbar) :
    (stableImage ρ hρ K hK g).map (fixedVectors ρ K.toSubgroup).subtype ≤
      (fixedVectors ρ C).map (Compact.averageMap ρ hρ K hK) := by
  obtain ⟨b, hb⟩ := exists_le_expandedLowerSubgroup_of_opposite hopp hMNbar C hC hCNbar
  calc
    _ ≤ (LinearMap.range (compressedAction ρ hρ K hK g ^ b)).map
        (fixedVectors ρ K.toSubgroup).subtype :=
      Submodule.map_mono (iInf_le _ b)
    _ = (fixedVectors ρ (expandedLowerSubgroup K Nbar g b)).map
        (Compact.averageMap ρ hρ K hK) :=
      compressionRange_eq_average_expandedLower_fixed ρ hρ hK h hcentral b
    _ ≤ _ := Submodule.map_mono (fixedVectors_antitone ρ hb)

end Langlands.Jacquet

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Averaged compact-fixed witnesses at cofinally many indices imply fixedness
of a completion family. The witnesses are averaged first to a compact core. -/
theorem componentsIn_le_completionFixed_of_average_fixed (H : Subgroup G)
    (hH : ∀ h ∈ H, ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ H ∧ h ∈ C)
    (S : Set (CompactOpenSubgroup G))
    (W : CompactOpenSubgroup G → Submodule ℂ V)
    (haverage : ∀ C : Subgroup G, IsCompact (C : Set G) → C ≤ H →
      IsCofinal {K : CompactOpenSubgroup G | K ∈ S ∧
        W K ≤ (fixedVectors ρ C).map (Compact.averageMap ρ hρ K.1 K.2)}) :
    componentsIn ρ hρ S W ≤ completionFixed ρ hρ H := by
  intro v hv
  apply (mem_completionFixed_iff_cofinal_fixed_components ρ hρ H hH v).mpr
  intro C hC hCH J
  obtain ⟨L, hLJ, hLC⟩ := J.exists_le_normalizedBy_compact C hC
  obtain ⟨K, ⟨hKS, hKW⟩, hKL⟩ := haverage C hC hCH L
  obtain ⟨w, hw, hweq⟩ := hKW (hv K hKS)
  have hLw : Compact.averageMap ρ hρ L.1 L.2 w = v.1 L := by
    calc
      _ = Compact.averageMap ρ hρ L.1 L.2
          (Compact.averageMap ρ hρ K.1 K.2 w) :=
        (Jacquet.averageMap_averageMap_of_le ρ hρ L.1 K.1 L.2 K.2 hKL w).symm
      _ = _ := by rw [hweq, v.property L K hKL]
  refine ⟨L, ?_, hLJ⟩
  intro c
  have hcavg := averageMap_translate ρ hρ (c : G) L w
  rw [hLC c⁻¹ (C.inv_mem c.property)] at hcavg
  change ρ (c : G) (v.1 L) = v.1 L
  rw [← hLw, ← hcavg]
  exact congrArg (Compact.averageMap ρ hρ L.1 L.2) (hw c)

end Langlands.CompactCompletion

namespace Langlands.Jacquet

open Langlands.HarishChandraSchwartz
open Langlands.CompactCompletion

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

omit [IsTopologicalGroup G] in
/-- Compact open indices with contractions in both orders for the fixed `g`. -/
def oppositeCompressionIndices (N M Nbar : Subgroup G) (g : G) :
    Set (CompactOpenSubgroup G) :=
  {K | IsIwahoriContraction K.1 N M Nbar g ∧
    IsIwahoriContraction K.1 Nbar M N g⁻¹}

/-- Completion families whose components at the opposite-contraction indices
lie in the ambient stable images. -/
def stableImageCompletion (N M Nbar : Subgroup G) (g : G) :
    Submodule ℂ (completion ρ hρ) :=
  componentsIn ρ hρ (oppositeCompressionIndices N M Nbar g)
    (fun K => (stableImage ρ hρ K.1 K.2 g).map
      (fixedVectors ρ K.1.toSubgroup).subtype)

/-- Stationary stable-image families are precisely the lower-fixed completion.
The opposite basis, normalizer, compact covering and stationarity inputs remain
explicit. -/
theorem stableImageCompletion_eq_completionFixed
    (N M Nbar : Subgroup G) (g : G)
    (hNbar : IsClosed (Nbar : Set G))
    (hMNbar : M ≤ Subgroup.normalizer Nbar)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (hBasis : HasOppositeIwahoriContractionBasis N M Nbar g)
    (hcover : ∀ h ∈ Nbar, ∃ C : Subgroup G,
      IsCompact (C : Set G) ∧ C ≤ Nbar ∧ h ∈ C)
    (hstationary : ∀ K ∈ oppositeCompressionIndices N M Nbar g,
      ∃ b : ℕ, stableImage ρ hρ K.1 K.2 g =
        LinearMap.range (compressedAction ρ hρ K.1 K.2 g ^ b)) :
    stableImageCompletion ρ hρ N M Nbar g = completionFixed ρ hρ Nbar := by
  apply le_antisymm
  · apply componentsIn_le_completionFixed_of_average_fixed ρ hρ Nbar hcover
    intro C hC hCNbar J
    obtain ⟨K, hK, hKJ, h, hopp⟩ := hBasis J.1 J.1.isOpen J.1.one_mem
    let L : CompactOpenSubgroup G := ⟨K, hK⟩
    exact ⟨L, ⟨⟨h, hopp⟩,
      stableImage_le_average_compact_fixed ρ hρ hK h hopp hcentral hMNbar C hC hCNbar⟩,
      hKJ⟩
  · intro v hv K hKS
    obtain ⟨C, hC, hCNbar, hCW⟩ :=
      exists_compact_average_fixed_le_stableImage ρ hρ K.2 hKS.1 hcentral hNbar
        (hMNbar hKS.1.mem_levi) (hstationary K hKS)
    have hcof := cofinal_fixed_components_of_fixed ρ hρ C hC v
      (fun c hc => hv c (hCNbar hc))
    obtain ⟨L, hLC, hLK⟩ := hcof K
    exact hCW ⟨v.1 L, hLC, v.property K L hLK⟩

end Langlands.Jacquet
