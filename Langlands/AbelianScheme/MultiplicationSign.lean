import Langlands.AbelianScheme.Multiplication
import Langlands.AbelianScheme.IsogenyStability

/-! # Inversion and signs in integer multiplication -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- Multiplication by minus one is an involutive automorphism. -/
noncomputable def multiplicationNegOneIso (G : Grp (Over S)) [IsCommMonObj G.X] :
    G ≅ G where
  hom := multiplication G (-1)
  inv := multiplication G (-1)
  hom_inv_id := by rw [← multiplication_mul]; norm_num
  inv_hom_id := by rw [← multiplication_mul]; norm_num

/-- Isomorphisms of group schemes are isogenies. -/
theorem isIsogeny_of_isIso {G H : Grp (Over S)} (f : G ⟶ H) [IsIso f] :
    IsIsogeny f := by
  have : IsIso f.hom.hom.left :=
    inferInstanceAs (IsIso ((Grp.forget (Over S) ⋙ Over.forget S).map f))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Inversion is a finite flat surjective morphism. -/
theorem isIsogeny_multiplication_neg_one (G : Grp (Over S)) [IsCommMonObj G.X] :
    IsIsogeny (multiplication G (-1)) :=
  isIsogeny_of_isIso (multiplicationNegOneIso G).hom

/-- Changing the sign of an integer preserves the isogeny property. -/
theorem isIsogeny_multiplication_neg_iff (G : Grp (Over S)) [IsCommMonObj G.X]
    (n : ℤ) : IsIsogeny (multiplication G (-n)) ↔ IsIsogeny (multiplication G n) := by
  have h (m : ℤ) (hm : IsIsogeny (multiplication G m)) :
      IsIsogeny (multiplication G (-m)) := by
    simpa only [← multiplication_mul, mul_neg_one] using
      hm.comp (isIsogeny_multiplication_neg_one G)
  exact ⟨fun hn => by simpa only [neg_neg] using h (-n) hn, h n⟩

/-- For any commutative group scheme, positive multiplication suffices for every
nonzero integer multiplication to be an isogeny. -/
theorem isIsogeny_multiplication_of_positive (G : Grp (Over S)) [IsCommMonObj G.X]
    (h : ∀ n : ℕ, 0 < n → IsIsogeny (multiplication G (n : ℤ)))
    (n : ℤ) (hn : n ≠ 0) : IsIsogeny (multiplication G n) := by
  cases n with
  | ofNat m => exact h m (Nat.pos_of_ne_zero (fun hm => hn (by simp [hm])))
  | negSucc m =>
      simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] using
        (isIsogeny_multiplication_neg_iff G ((m + 1 : ℕ) : ℤ)).mpr (h (m + 1) (by omega))

end Langlands.GroupScheme
