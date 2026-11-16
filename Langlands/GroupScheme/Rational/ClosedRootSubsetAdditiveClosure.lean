import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- A closed subset of a finite crystallographic root pairing is saturated
among roots for positive integral sums, including an empty sum. -/
theorem rootPairing_mem_of_mem_addSubmonoidClosure
    {J V W : Type*} [Finite J] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (P : RootPairing J ℚ V W) [P.IsCrystallographic]
    {Y : Set V} (hY : Y ⊆ Set.range P.root)
    (hadd : ∀ a ∈ Y, ∀ b ∈ Y, a + b ∈ Set.range P.root → a + b ∈ Y)
    {a : V} (ha : a ∈ Set.range P.root)
    (hgen : a ∈ AddSubmonoid.closure Y) : a ∈ Y := by
  classical
  obtain ⟨L, hL, rfl⟩ := AddSubmonoid.exists_multiset_of_mem_closure hgen
  clear hgen
  induction L using Multiset.strongInductionOn with
  | ih L ih =>
    obtain ⟨j, hj⟩ := ha
    have hpos : 0 < (L.map (P.coroot' j)).sum := by
      rw [← map_multiset_sum, ← hj]
      simp
    obtain ⟨x, hx, hxpos⟩ : ∃ x ∈ L, 0 < P.coroot' j x := by
      by_contra! hn
      have hnonpos : (L.map (P.coroot' j)).sum ≤ 0 := by
        apply Multiset.sum_nonneg (α := ℚᵒᵈ)
        intro q hq
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hq
        exact hn x hx
      exact (not_lt_of_ge hnonpos) hpos
    by_cases hxeq : x = L.sum
    · exact hxeq ▸ hL x hx
    obtain ⟨i, hi⟩ := hY (hL x hx)
    have hij : i ≠ j := by
      intro heq
      exact hxeq (hi.symm.trans (heq ▸ hj))
    have hpair : 0 < P.pairingIn ℤ i j := by
      have hp : (0 : ℚ) < P.pairing i j := by
        simpa only [← hi, P.root_coroot'_eq_pairing] using hxpos
      exact_mod_cast (show (0 : ℚ) < (P.pairingIn ℤ i j : ℚ) by
        change 0 < algebraMap ℤ ℚ (P.pairingIn ℤ i j)
        rw [P.algebraMap_pairingIn]
        exact hp)
    have hsub : L.sum - x ∈ Set.range P.root := by
      rw [← hj, ← hi, ← neg_sub, RootPairing.neg_mem_range_root_iff]
      exact P.root_sub_root_mem_of_pairingIn_pos hpair hij
    have herase : (L.erase x).sum = L.sum - x := by
      have he := Multiset.sum_erase hx
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)
    have hsmaller : (L.erase x).sum ∈ Y :=
      ih (L.erase x) (Multiset.erase_lt.mpr hx)
        (fun y hy => hL y (Multiset.mem_of_mem_erase hy)) (herase ▸ hsub)
    have h := hadd x (hL x hx) (L.erase x).sum hsmaller (by
      rw [Multiset.sum_erase hx]
      exact ⟨j, hj⟩)
    simpa only [Multiset.sum_erase hx] using h

/-- Closed subsets of the actual, possibly nonreduced relative roots contain
every relative root in their additive monoid. -/
theorem IsClosedRootSubset.mem_of_mem_addSubmonoidClosure
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    {S : Set (characterLattice T)}
    (hS : letI := hG.isAffineHom; IsClosedRootSubset (relativeRoots i) S)
    {a : characterLattice T}
    (ha : letI := hG.isAffineHom; a ∈ relativeRoots i)
    (hgen : a ∈ AddSubmonoid.closure S) : a ∈ S := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  obtain ⟨J, hJ, P, _, hcr, _, hroots, _, _⟩ := relativeRootSystem k G hG T i hi
  let := hJ
  let := hcr
  have hinj := hi.isSplitSubtorus.1.character_toRat_injective
  let Y : Set (relativeRootSpan i) := {y | ∃ χ ∈ S, toRat χ = y.val}
  have hroot_iff (y : relativeRootSpan i) :
      y ∈ Set.range P.root ↔ ∃ χ ∈ relativeRoots i, toRat χ = y.val := by
    constructor
    · intro hy
      change y.val ∈ toRat '' relativeRoots i
      exact hroots ▸ (show y.val ∈ Subtype.val '' Set.range P.root from ⟨y, hy, rfl⟩)
    · intro hy
      have hymem : y.val ∈ toRat '' relativeRoots i := hy
      rw [← hroots] at hymem
      obtain ⟨z, hz, hzy⟩ := hymem
      exact (Subtype.ext hzy : z = y) ▸ hz
  have hY : Y ⊆ Set.range P.root := by
    rintro y ⟨χ, hχ, hχy⟩
    exact (hroot_iff y).mpr ⟨χ, hS.1 hχ, hχy⟩
  have hadd : ∀ x ∈ Y, ∀ y ∈ Y, x + y ∈ Set.range P.root → x + y ∈ Y := by
    intro x hx y hy hxy
    obtain ⟨β, hβ, hβx⟩ := hx
    obtain ⟨ψ, hψ, hψy⟩ := hy
    obtain ⟨χ, hχ, he⟩ := (hroot_iff (x + y)).mp hxy
    have heq : toRat (β + ψ) = toRat χ := by
      rw [map_add, hβx, hψy, he]
      rfl
    refine ⟨β + ψ, hS.2 β hβ ψ hψ ?_, ?_⟩
    · rw [hinj heq]
      exact hχ
    · rw [map_add, hβx, hψy]
      rfl
  have hlift : ∀ χ ∈ AddSubmonoid.closure S,
      ∃ y ∈ AddSubmonoid.closure Y, y.val = toRat χ := by
    intro χ hχ
    induction hχ using AddSubmonoid.closure_induction with
    | mem χ hχ =>
      exact ⟨⟨toRat χ, toRat_mem_ratSpan (hS.1 hχ)⟩,
        AddSubmonoid.subset_closure ⟨χ, hχ, rfl⟩, rfl⟩
    | zero =>
      exact ⟨0, (AddSubmonoid.closure Y).zero_mem, by simp⟩
    | add χ ψ _ _ hχ hψ =>
      obtain ⟨x, hx, hxe⟩ := hχ
      obtain ⟨y, hy, hye⟩ := hψ
      exact ⟨x + y, (AddSubmonoid.closure Y).add_mem hx hy, by
        change x.val + y.val = toRat (χ + ψ)
        rw [map_add, hxe, hye]⟩
  obtain ⟨y, hy, hye⟩ := hlift a hgen
  have hyroot : y ∈ Set.range P.root := (hroot_iff y).mpr ⟨a, ha, hye.symm⟩
  obtain ⟨β, hβ, hβy⟩ := rootPairing_mem_of_mem_addSubmonoidClosure P hY hadd hyroot hy
  exact hinj (hβy.trans hye) ▸ hβ

end Langlands.GroupScheme
