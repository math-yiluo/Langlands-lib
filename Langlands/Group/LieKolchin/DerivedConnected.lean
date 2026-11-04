import Mathlib.GroupTheory.Solvable
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Basic

/-! # Connected derived subgroups for separately continuous group laws -/

open scoped commutatorElement

namespace Langlands.LieKolchin

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The commutator subgroup of a subgroup whose underlying set is preconnected is connected,
provided left translations, inversion and every map `y ↦ ⁅a, y⁆` are continuous. -/
theorem isConnected_commutator
    (hmul : ∀ a : G, Continuous fun x => a * x) (hinv : Continuous fun x : G => x⁻¹)
    (hcomm : ∀ a : G, Continuous fun x : G => ⁅a, x⁆)
    {Γ : Subgroup G} (hΓ : IsPreconnected (Γ : Set G)) :
    IsConnected ((⁅Γ, Γ⁆ : Subgroup G) : Set G) := by
  set H : Subgroup G := ⁅Γ, Γ⁆
  set K : Set G := connectedComponentIn (H : Set G) 1
  have h1 : (1 : G) ∈ (H : Set G) := H.one_mem
  have hK : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKH : K ⊆ H := connectedComponentIn_subset _ _
  have h1K : (1 : G) ∈ K := mem_connectedComponentIn h1
  let K' : Subgroup G :=
    { carrier := K
      one_mem' := h1K
      mul_mem' := fun {a b} ha hb => by
        have hpre : IsPreconnected ((fun x => a * x) '' K) :=
          hK.image _ (hmul a).continuousOn
        have hsub : (fun x => a * x) '' K ⊆ H := by
          rintro _ ⟨x, hx, rfl⟩
          exact H.mul_mem (hKH ha) (hKH hx)
        have ha' : a ∈ (fun x => a * x) '' K := ⟨1, h1K, mul_one a⟩
        have := hpre.subset_connectedComponentIn ha' hsub
        rw [← connectedComponentIn_eq ha] at this
        exact this ⟨b, hb, rfl⟩
      inv_mem' := fun {a} ha => by
        have hpre : IsPreconnected ((fun x : G => x⁻¹) '' K) :=
          hK.image _ hinv.continuousOn
        have hsub : (fun x : G => x⁻¹) '' K ⊆ H := by
          rintro _ ⟨x, hx, rfl⟩
          exact H.inv_mem (hKH hx)
        have h1' : (1 : G) ∈ (fun x : G => x⁻¹) '' K := ⟨1, h1K, inv_one⟩
        exact hpre.subset_connectedComponentIn h1' hsub ⟨a, ha, rfl⟩ }
  have hle : H ≤ K' := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hpre : IsPreconnected ((fun z => ⁅x, z⁆) '' (Γ : Set G)) :=
      hΓ.image _ (hcomm x).continuousOn
    have hsub : (fun z => ⁅x, z⁆) '' (Γ : Set G) ⊆ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact Subgroup.commutator_mem_commutator hx hz
    have h1' : (1 : G) ∈ (fun z => ⁅x, z⁆) '' (Γ : Set G) :=
      ⟨1, Γ.one_mem, commutatorElement_one_right x⟩
    exact hpre.subset_connectedComponentIn h1' hsub ⟨y, hy, rfl⟩
  have hHK : (H : Set G) = K := le_antisymm (fun x hx => hle hx) hKH
  rw [hHK]
  exact isConnected_connectedComponentIn_iff.2 h1

/-- Every term of the derived series of a connected group is connected under the same
separate continuity hypotheses. -/
theorem isConnected_derivedSeries [PreconnectedSpace G]
    (hmul : ∀ a : G, Continuous fun x => a * x) (hinv : Continuous fun x : G => x⁻¹)
    (hcomm : ∀ a : G, Continuous fun x : G => ⁅a, x⁆) (n : ℕ) :
    IsConnected (derivedSeries G n : Set G) := by
  induction n with
  | zero =>
    rw [derivedSeries_zero, Subgroup.coe_top]
    exact ⟨Set.univ_nonempty, isPreconnected_univ⟩
  | succ n ih =>
    rw [derivedSeries_succ]
    exact isConnected_commutator hmul hinv hcomm ih.isPreconnected

/-- A preconnected set covered by finitely many closed sets that are pairwise disjoint on it
lies in any one of them that it meets. -/
theorem subset_of_finite_closed_cover {X ι : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {t : Set ι} (ht : t.Finite) (A : ι → Set X)
    (hA : ∀ i ∈ t, IsClosed (A i)) (hcover : s ⊆ ⋃ i ∈ t, A i)
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → ∀ x ∈ s, x ∈ A i → x ∉ A j)
    {i₀ : ι} (hi₀ : i₀ ∈ t) {x₀ : X} (hx₀ : x₀ ∈ s) (hx₀' : x₀ ∈ A i₀) : s ⊆ A i₀ := by
  set B : Set X := ⋃ i ∈ t \ {i₀}, A i
  have hB : IsClosed B := (ht.sdiff (t := {i₀})).isClosed_biUnion fun i hi => hA i hi.1
  have hsub : s ⊆ A i₀ ∪ B := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hcover hx)
    by_cases h : i = i₀
    · exact Or.inl (h ▸ hxi)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, ⟨hi, h⟩, hxi⟩)
  have hempty : s ∩ (A i₀ ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx₁, hx₂⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx₂
    exact hdisj i₀ hi₀ i hi.1 (Ne.symm hi.2) x hx hx₁ hxi
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hs _ _ (hA i₀ hi₀) hB hsub hempty
    with h | h
  · exact h
  · exfalso
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (h hx₀)
    exact hdisj i₀ hi₀ i hi.1 (Ne.symm hi.2) x₀ hx₀ hx₀' hxi

end Langlands.LieKolchin
