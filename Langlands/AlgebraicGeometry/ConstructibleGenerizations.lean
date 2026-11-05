import Langlands.Algebra.NagataOpennessCriterion
import Mathlib.Topology.Constructible

/-! # Pointwise interior of constructible sets in Noetherian sober spaces -/

noncomputable section

universe u

open Set Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- The points all of whose generalizations lie in a prescribed subset. -/
def generalizationInterior {T : Type u} [TopologicalSpace T] (S : Set T) : Set T :=
  {x | ∀ y : T, y ⤳ x → y ∈ S}

/-- A constructible set has constant membership near the generic point of any subset. -/
theorem exists_open_constructible_membership_on_generic
    {T : Type u} [TopologicalSpace T] {η : T} {Z S : Set T}
    (hη : IsGenericPoint η Z) (hs : IsConstructible S) :
    ∃ U : Set T, IsOpen U ∧ η ∈ U ∧
      ∀ x ∈ Z ∩ U, (x ∈ S ↔ η ∈ S) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : η ∈ U
    · exact ⟨U, hU, h, fun _ hx => ⟨fun _ => h, fun _ => hx.2⟩⟩
    · refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
      intro x hx
      have hx' : x ∉ U := by
        intro hxu
        exact h ((hη.mem_open_set_iff hU).mpr ⟨x, hx.1, hxu⟩)
      simp only [hx', h]
  | union s hs t ht ihs iht =>
    obtain ⟨U, hU, hηU, hsU⟩ := ihs
    obtain ⟨V, hV, hηV, htV⟩ := iht
    refine ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, ?_⟩
    intro x hx
    exact or_congr (hsU x ⟨hx.1, hx.2.1⟩) (htV x ⟨hx.1, hx.2.2⟩)
  | compl s hs ih =>
    obtain ⟨U, hU, hηU, hsU⟩ := ih
    exact ⟨U, hU, hηU, fun x hx => not_congr (hsU x hx)⟩

/-- Every point in the closure of a constructible subset of a Noetherian sober space
is a specialization of a point of the subset. -/
theorem exists_specializes_of_mem_closure_of_isConstructible
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {S : Set T} (hs : IsConstructible S) {x : T} (hx : x ∈ closure S) :
    ∃ y ∈ S, y ⤳ x := by
  classical
  obtain ⟨F, hF, hcover, hirredundant⟩ :=
    Langlands.Algebra.exists_finset_isClosed_isIrreducible_irredundant
      (isClosed_closure (s := S))
  obtain ⟨Z, hZF, hxZ⟩ := Set.mem_iUnion₂.mp (hcover ▸ hx)
  obtain ⟨hZc, hZi⟩ := hF Z hZF
  let η := hZi.genericPoint
  have hη : IsGenericPoint η Z := hZi.isGenericPoint_genericPoint hZc
  have hηZ : η ∈ Z := hη.mem
  have hηS : η ∈ S := by
    by_contra hηS
    obtain ⟨U, hU, hηU, hconst⟩ :=
      exists_open_constructible_membership_on_generic hη hs
    let W := ⋃ Z' ∈ F.erase Z, Z'
    have hW : IsClosed W :=
      (F.erase Z).finite_toSet.isClosed_biUnion fun Z' hZ' =>
        (hF Z' (Finset.mem_of_mem_erase hZ')).1
    have hηW : η ∉ W := by
      intro hh
      have hZW : Z ⊆ W := by
        rw [← hη.def]
        exact hW.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hh)
      exact hirredundant Z hZF hZW
    have hηclosure : η ∈ closure S := hcover ▸ Set.mem_iUnion₂.mpr ⟨Z, hZF, hηZ⟩
    obtain ⟨y, ⟨hyU, hyW⟩, hyS⟩ := mem_closure_iff.mp hηclosure
      (U ∩ Wᶜ) (hU.inter hW.isOpen_compl) ⟨hηU, hηW⟩
    have hyZ : y ∈ Z := by
      obtain ⟨Z', hZ'F, hyZ'⟩ :=
        Set.mem_iUnion₂.mp (hcover ▸ (subset_closure hyS : y ∈ closure S))
      by_contra hn
      have hne : Z' ≠ Z := fun hh => hn (hh ▸ hyZ')
      exact hyW (Set.mem_iUnion₂.mpr ⟨Z', Finset.mem_erase.mpr ⟨hne, hZ'F⟩, hyZ'⟩)
    exact hηS ((hconst y ⟨hyZ, hyU⟩).mp hyS)
  exact ⟨η, hηS, specializes_iff_mem_closure.mpr (hη.def ▸ hxZ)⟩

/-- On a constructible subset of a Noetherian sober space, the generalization
condition characterizes interior membership. -/
theorem interior_eq_generalizationInterior_of_isConstructible
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {S : Set T} (hs : IsConstructible S) :
    interior S = generalizationInterior S := by
  ext x
  constructor
  · intro hx y hy
    exact interior_subset (hy.mem_open isOpen_interior hx)
  · intro hx
    by_contra hxi
    have hcl : x ∈ closure Sᶜ := by
      simpa only [closure_compl, Set.mem_compl_iff] using hxi
    obtain ⟨y, hyS, hyx⟩ := exists_specializes_of_mem_closure_of_isConstructible hs.compl hcl
    exact hyS (hx y hyx)

/-- The pointwise form used to turn generization stability into a neighbourhood. -/
theorem mem_interior_of_isConstructible_of_generizations
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {S : Set T} (hs : IsConstructible S) {x : T}
    (hx : ∀ y : T, y ⤳ x → y ∈ S) : x ∈ interior S := by
  rw [interior_eq_generalizationInterior_of_isConstructible hs]
  exact hx

end Langlands.AlgebraicGeometry
