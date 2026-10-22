import Langlands.Topology.GroupAction.FiniteOrbitStatement
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! Proof of finite orbit ordering for sigma-compact continuous group actions. -/

namespace Langlands.Topology

open Set MulAction
open scoped Pointwise

universe uH uX

namespace FiniteOrbitProof

variable {H : Type uH} [Group H] [TopologicalSpace H] [SigmaCompactSpace H]
  {X : Type uX} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MulAction H X] [ContinuousSMul H X]

/-- A nonempty closed invariant set contains an orbit that is the trace on it of an
open set. -/
theorem exists_relOpen_orbit [Finite (orbitRel.Quotient H X)] {C : Set X}
    (hC : IsClosed C) (hinv : ∀ (h : H) (x : X), x ∈ C → h • x ∈ C)
    (hne : C.Nonempty) :
    ∃ y ∈ C, ∃ V : Set X, IsOpen V ∧ V ∩ C = orbit H y := by
  have : LocallyCompactSpace C := hC.locallyCompactSpace
  have : Nonempty C := hne.to_subtype
  -- Compact pieces of the orbits: images of the compact covering of `H`.
  let A : orbitRel.Quotient H X × ℕ → Set X := fun p =>
    (fun h : H => h • p.1.out) '' compactCovering H p.2
  have hA_closed : ∀ p, IsClosed (A p) := fun p =>
    ((isCompact_compactCovering H p.2).image (continuous_id.smul continuous_const)).isClosed
  have hA_orbit : ∀ p, A p ⊆ orbit H p.1.out := by
    rintro p _ ⟨h, -, rfl⟩
    exact mem_orbit _ h
  have hA_cover : ⋃ p, A p = univ := by
    refine eq_univ_of_forall fun z => ?_
    have hz : (Quotient.mk (orbitRel H X) z).out ∈ orbit H z :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) z))
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (mem_orbit_symm.mp hz)
    have hgU : g ∈ ⋃ m, compactCovering H m := by
      rw [iUnion_compactCovering]
      exact mem_univ g
    obtain ⟨m, hm⟩ := mem_iUnion.mp hgU
    exact mem_iUnion.mpr ⟨(Quotient.mk (orbitRel H X) z, m), g, hm, hg⟩
  -- Baire category in the closed subspace `C`.
  let f : orbitRel.Quotient H X × ℕ → Set C := fun p => Subtype.val ⁻¹' A p
  have hf_closed : ∀ p, IsClosed (f p) := fun p =>
    (hA_closed p).preimage continuous_subtype_val
  have hf_cover : ⋃ p, f p = univ := by
    simp only [f, ← preimage_iUnion, hA_cover, preimage_univ]
  obtain ⟨p, hp⟩ := nonempty_interior_of_iUnion_of_closed hf_closed hf_cover
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp (isOpen_interior (s := f p))
  obtain ⟨⟨y, hyC⟩, hy⟩ := hp
  have hyW : y ∈ W := by
    have : (⟨y, hyC⟩ : C) ∈ Subtype.val ⁻¹' W := by rw [hWeq]; exact hy
    exact this
  have hWC : W ∩ C ⊆ orbit H y := by
    rintro z ⟨hzW, hzC⟩
    have h1 : (⟨z, hzC⟩ : C) ∈ interior (f p) := by rw [← hWeq]; exact hzW
    have h1' : (⟨z, hzC⟩ : C) ∈ f p := interior_subset h1
    have hy' : (⟨y, hyC⟩ : C) ∈ f p := interior_subset hy
    have h2 : z ∈ orbit H p.1.out := hA_orbit p h1'
    have h3 : y ∈ orbit H p.1.out := hA_orbit p hy'
    rw [← orbit_eq_iff] at h3
    rwa [h3]
  -- Translating `W` throughout `H` gives the required open set.
  refine ⟨y, hyC, ⋃ h : H, h • W, isOpen_iUnion fun h => hW.smul h, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨h, hz⟩, hzC⟩
    rw [mem_smul_set_iff_inv_smul_mem] at hz
    have h1 := mem_orbit_of_mem_orbit h (hWC ⟨hz, hinv _ _ hzC⟩)
    rwa [smul_inv_smul] at h1
  · intro hz
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hz
    exact ⟨⟨g, smul_mem_smul_set hyW⟩, hinv g y hyC⟩

/-- Every closed invariant set `C` has an orbit enumeration whose initial unions,
together with the complement of `C`, are open. Induction on the number of orbits
meeting `C`. -/
theorem exists_ordering_of_closed [Finite (orbitRel.Quotient H X)] (N : ℕ) :
    ∀ C : Set X, IsClosed C → (∀ (h : H) (x : X), x ∈ C → h • x ∈ C) →
    (Quotient.mk (orbitRel H X) '' C).ncard = N →
    ∃ (n : ℕ) (r : Fin n → X), (∀ i, r i ∈ C) ∧
      (∀ x ∈ C, ∃ i, x ∈ orbit H (r i)) ∧
      Pairwise (fun i j => Disjoint (orbit H (r i)) (orbit H (r j))) ∧
      ∀ k : Fin (n + 1),
        IsOpen (Cᶜ ∪ {x : X | ∃ i : Fin n, i.val < k.val ∧ x ∈ orbit H (r i)}) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C hC hinv hN
  rcases C.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, Fin.elim0, fun i => i.elim0, fun x hx => hx.elim, fun i => i.elim0,
      fun k => ?_⟩
    simp
  obtain ⟨y, hyC, V, hV, hVC⟩ := exists_relOpen_orbit hC hinv hne
  have horbV : orbit H y ⊆ V := hVC ▸ inter_subset_left
  have hVC' : ∀ x ∈ V, x ∈ C → x ∈ orbit H y := fun x hxV hxC => hVC ▸ ⟨hxV, hxC⟩
  have hC' : IsClosed (C ∩ Vᶜ) := hC.inter hV.isClosed_compl
  have hinv' : ∀ (h : H) (x : X), x ∈ C ∩ Vᶜ → h • x ∈ C ∩ Vᶜ := by
    rintro h x ⟨hxC, hxV⟩
    refine ⟨hinv h x hxC, fun hhx => hxV ?_⟩
    have h1 := mem_orbit_of_mem_orbit h⁻¹ (hVC' _ hhx (hinv h x hxC))
    rw [inv_smul_smul] at h1
    exact horbV h1
  have hlt : (Quotient.mk (orbitRel H X) '' (C ∩ Vᶜ)).ncard < N := by
    rw [← hN]
    refine ncard_lt_ncard ⟨image_mono inter_subset_left, fun hsub => ?_⟩
    obtain ⟨z, ⟨-, hzV⟩, hz⟩ := hsub (mem_image_of_mem _ hyC)
    have hzy : z ∈ orbit H y := Quotient.exact hz
    exact hzV (horbV hzy)
  obtain ⟨n, r, hrC, hcov, hdisj, hopen⟩ := ih _ hlt (C ∩ Vᶜ) hC' hinv' rfl
  have hdisj0 : ∀ j, Disjoint (orbit H y) (orbit H (r j)) := by
    intro j
    rw [Set.disjoint_left]
    intro z hzy hzr
    have hrj : orbit H (r j) = orbit H y := by
      rw [← orbit_eq_iff.mpr hzr, orbit_eq_iff.mpr hzy]
    apply (hrC j).2
    apply horbV
    rw [← hrj]
    exact mem_orbit_self _
  refine ⟨n + 1, Fin.cons y r, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hyC
    | succ j => simpa using (hrC j).1
  · intro x hx
    by_cases hxV : x ∈ V
    · exact ⟨0, by simpa using hVC' x hxV hx⟩
    · obtain ⟨j, hj⟩ := hcov x ⟨hx, hxV⟩
      exact ⟨j.succ, by simpa using hj⟩
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simpa using hdisj0 j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using (hdisj0 i).symm
      | succ j => simpa using hdisj (fun h => hij (by rw [h]))
  · intro k
    induction k using Fin.cases with
    | zero => simpa using hC.isOpen_compl
    | succ k =>
      have hset : {x : X | ∃ i : Fin (n + 1), i.val < k.succ.val ∧
            x ∈ orbit H ((Fin.cons y r : Fin (n + 1) → X) i)} =
          orbit H y ∪ {x : X | ∃ j : Fin n, j.val < k.val ∧ x ∈ orbit H (r j)} := by
        ext x
        simp only [mem_ofPred_eq, mem_union, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ,
          Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, true_and, add_lt_add_iff_right]
      rw [hset]
      convert hopen k using 1
      ext x
      simp only [mem_union, mem_compl_iff, mem_inter_iff, not_and, not_not]
      constructor
      · rintro (hxC | hxy | hxS)
        · exact Or.inl fun h => absurd h hxC
        · exact Or.inl fun _ => horbV hxy
        · exact Or.inr hxS
      · rintro (hx | hxS)
        · by_cases hxC : x ∈ C
          · exact Or.inr (Or.inl (hVC' x (hx hxC) hxC))
          · exact Or.inl hxC
        · exact Or.inr (Or.inr hxS)

end FiniteOrbitProof

open FiniteOrbitProof in
/-- Finite orbit ordering for continuous actions of sigma-compact topological groups
on locally compact Hausdorff spaces. -/
theorem finiteOrbitOrdering : FiniteOrbitOrdering.{uH, uX} := by
  intro H _ _ _ _ X _ _ _ _ _ hfin
  obtain ⟨n, r, -, hcov, hdisj, hopen⟩ :=
    exists_ordering_of_closed (H := H) (X := X) _ univ isClosed_univ
      (fun _ _ _ => mem_univ _) rfl
  refine ⟨n, r, fun x => hcov x (mem_univ x), hdisj, fun k => ?_⟩
  simpa using hopen k

end Langlands.Topology
