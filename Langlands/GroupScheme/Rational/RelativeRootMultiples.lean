import Langlands.GroupScheme.Rational.Statement
import Mathlib.Data.Nat.Prime.Defs

/-! # Positive integral multiples in a possibly nonreduced relative root system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace RootPairing

variable {J M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N]

/-- A crystallographic root pairing admits only the first and second positive
integral multiples of any one root. Reducedness and finiteness are unnecessary. -/
theorem eq_one_or_two_of_root_eq_nsmul (P : RootPairing J ℚ M N)
    [P.IsCrystallographic] {a b : J} {n : ℕ} (h : P.root b = n • P.root a) :
    n = 1 ∨ n = 2 := by
  have hq : (2 : ℚ) = (n : ℚ) * P.pairing a b := by
    simpa only [map_nsmul, root_coroot'_eq_pairing, pairing_same, nsmul_eq_mul] using
      congrArg (P.coroot' b) h
  have hc : (P.pairingIn ℤ a b : ℚ) = P.pairing a b :=
    P.algebraMap_pairingIn ℤ a b
  rw [← hc] at hq
  have hz : (2 : ℤ) = (n : ℤ) * P.pairingIn ℤ a b := by
    exact_mod_cast hq
  have hd : (n : ℤ) ∣ (2 : ℤ) := ⟨_, hz⟩
  exact (Nat.dvd_prime Nat.prime_two).mp (Int.natCast_dvd_natCast.mp hd)

end RootPairing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- The natural-number multipliers whose character multiples are actual
relative roots. The zero multiplier is excluded by the actual root definition. -/
def relativeRootMultipliers (i : T.toGrp ⟶ G) (a : characterLattice T) : Set ℕ :=
  {n | n • a ∈ relativeRoots i}

/-- The published root-system predicate bounds every natural multiple of an
actual relative root, without a reducedness hypothesis. -/
theorem HasRelativeRootSystem.eq_one_or_two_of_nsmul_mem (hR : HasRelativeRootSystem i)
    {a : characterLattice T} (ha : a ∈ relativeRoots i) {n : ℕ}
    (hn : n • a ∈ relativeRoots i) : n = 1 ∨ n = 2 := by
  obtain ⟨J, hJ, P, _, hP, _, hroot, _, _⟩ := hR
  let := hP
  have ha' : toRat a ∈ Subtype.val '' Set.range P.root := by
    rw [hroot]
    exact Set.mem_image_of_mem _ ha
  have hn' : toRat (n • a) ∈ Subtype.val '' Set.range P.root := by
    rw [hroot]
    exact Set.mem_image_of_mem _ hn
  obtain ⟨v, ⟨r, rfl⟩, hr⟩ := ha'
  obtain ⟨w, ⟨s, rfl⟩, hs⟩ := hn'
  apply P.eq_one_or_two_of_root_eq_nsmul (a := r) (b := s)
  apply Subtype.ext
  change (P.root s).val = n • (P.root r).val
  rw [hs, hr, map_nsmul]

/-- No third or later positive integral multiple is an actual relative root. -/
theorem HasRelativeRootSystem.nsmul_not_mem_of_three_le (hR : HasRelativeRootSystem i)
    {a : characterLattice T} (ha : a ∈ relativeRoots i) {n : ℕ} (hn : 3 ≤ n) :
    n • a ∉ relativeRoots i := by
  intro hna
  rcases hR.eq_one_or_two_of_nsmul_mem ha hna with h | h <;> omega

/-- If the doubled root is absent, every relative root on the positive integral
ray of a is the first root. -/
theorem HasRelativeRootSystem.eq_one_of_nsmul_mem_of_two_not_mem
    (hR : HasRelativeRootSystem i) {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (h2 : 2 • a ∉ relativeRoots i) {n : ℕ} (hn : n • a ∈ relativeRoots i) : n = 1 := by
  rcases hR.eq_one_or_two_of_nsmul_mem ha hn with h | h
  · exact h
  · exact False.elim (h2 (h ▸ hn))

/-- The actual multipliers lie in the two-element set allowed for nonreduced roots. -/
theorem HasRelativeRootSystem.relativeRootMultipliers_subset
    (hR : HasRelativeRootSystem i) {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    relativeRootMultipliers i a ⊆ ({1, 2} : Set ℕ) := by
  intro n hn
  rcases hR.eq_one_or_two_of_nsmul_mem ha hn with h | h <;> simp [h]

end Langlands.GroupScheme
