import Langlands.LinearAlgebra.CartanENumbering
import Langlands.LinearAlgebra.RootReflectionCoefficients

/-! # The E6 Cartan symmetry and an actual root certificate -/

noncomputable section

namespace Langlands.CartanE6Root

open RootReflectionCoefficients CartanWalkColor

/-- Exchange the two equal arms of the standard E6 diagram. -/
def symmetry : Equiv.Perm (Fin 6) :=
  Function.Involutive.toPerm (![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6)
    (by intro i; fin_cases i <;> rfl)

@[simp] theorem symmetry_apply (i : Fin 6) :
    symmetry i = (![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) i := rfl

/-- The coefficient vector in the actual-root certificate. -/
def coefficients : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]

/-- Sum the coefficients over the opposition orbit, counting a fixed vertex once. -/
theorem sum_coefficients_symmetry (j : Fin 6) :
    (∑ i : Fin 6, if i = j ∨ i = symmetry j then coefficients i else 0) =
      (![2, 2, 4, 3, 4, 2] : Fin 6 → ℤ) j := by
  have h : ∀ j : Fin 6,
      (∑ i : Fin 6, if i = j ∨ i = symmetry j then coefficients i else 0) =
        (![2, 2, 4, 3, 4, 2] : Fin 6 → ℤ) j := by decide
  exact h j

/-- Every E6 Cartan symmetry is globally identity or the arm exchange. -/
theorem eq_id_or_symmetry_of_preserves (f : Fin 6 → Fin 6)
    (hf : ∀ i j, CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j) :
    (∀ i, f i = i) ∨ (∀ i, f i = symmetry i) := by
  have hinj := CartanENumbering.injective_of_preserves f hf
  have hbij : Function.Bijective f := (Finite.injective_iff_bijective).mp hinj
  have h1 : step (CartanMatrix.E 6) (fun _ => 1) =
      ![1, 1, 2, 3, 2, 1] := by decide
  have h2 : step (CartanMatrix.E 6) ![1, 1, 2, 3, 2, 1] =
      ![2, 3, 4, 5, 4, 2] := by decide
  have hi1 := step_invariant hf hbij (c := fun _ => 1) (fun _ => rfl)
  rw [h1] at hi1
  have hi2 := step_invariant hf hbij hi1
  rw [h2] at hi2
  have hfiber : ∀ i j : Fin 6,
      (![2, 3, 4, 5, 4, 2] : Fin 6 → ℕ) j =
        (![2, 3, 4, 5, 4, 2] : Fin 6 → ℕ) i →
      j = i ∨ j = symmetry i := by decide
  have him (i : Fin 6) := hfiber i (f i) (hi2 i)
  have hfix1 : f 1 = 1 := by simpa using him 1
  have hfix3 : f 3 = 3 := by simpa using him 3
  rcases him 0 with h0 | h0
  · have h5 : f 5 = 5 := by
      rcases him 5 with h5 | h5
      · exact h5
      · have hne : (5 : Fin 6) ≠ 0 := by decide
        exact (hne (hinj (h5.trans h0.symm))).elim
    have h2 : f 2 = 2 := by
      rcases him 2 with h2 | h2
      · exact h2
      · have h := hf 0 2
        simp [h0, h2, CartanMatrix.E] at h
    have h4 : f 4 = 4 := by
      rcases him 4 with h4 | h4
      · exact h4
      · have hne : (4 : Fin 6) ≠ 2 := by decide
        exact (hne (hinj (h4.trans h2.symm))).elim
    left
    intro i
    fin_cases i <;> assumption
  · have h5 : f 5 = 0 := by
      rcases him 5 with h5 | h5
      · have hne : (5 : Fin 6) ≠ 0 := by decide
        exact (hne (hinj (h5.trans h0.symm))).elim
      · exact h5
    have h2 : f 2 = 4 := by
      rcases him 2 with h2 | h2
      · have h := hf 0 2
        simp [h0, h2, CartanMatrix.E] at h
      · exact h2
    have h4 : f 4 = 2 := by
      rcases him 4 with h4 | h4
      · have hne : (4 : Fin 6) ≠ 2 := by decide
        exact (hne (hinj (h4.trans h2.symm))).elim
      · exact h4
    right
    intro i
    fin_cases i <;> first | exact h0 | exact hfix1 | exact h2 | exact hfix3 | exact h4 | exact h5

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (a : Fin 6 → J)

/-- An explicit reflection sequence constructs an actual root with these coefficients. -/
theorem isRoot_highest
    (hM : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.E 6 i j) :
    IsRoot P a coefficients := by
  have h0 : IsRoot P a ![0, 0, 0, 0, 0, 1] := by
    convert isRoot_single P a (5 : Fin 6) using 1
    ext i
    fin_cases i <;> simp
  have h1 : IsRoot P a ![0, 0, 0, 0, 1, 1] := by
    have he : reflect (CartanMatrix.E 6) 4 ![0, 0, 0, 0, 0, 1] =
        ![0, 0, 0, 0, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h0 (CartanMatrix.E 6) hM 4
  have h2 : IsRoot P a ![0, 0, 0, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 6) 3 ![0, 0, 0, 0, 1, 1] =
        ![0, 0, 0, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h1 (CartanMatrix.E 6) hM 3
  have h3 : IsRoot P a ![0, 0, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 6) 2 ![0, 0, 0, 1, 1, 1] =
        ![0, 0, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h2 (CartanMatrix.E 6) hM 2
  have h4 : IsRoot P a ![0, 1, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 6) 1 ![0, 0, 1, 1, 1, 1] =
        ![0, 1, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h3 (CartanMatrix.E 6) hM 1
  have h5 : IsRoot P a ![0, 1, 1, 2, 1, 1] := by
    have he : reflect (CartanMatrix.E 6) 3 ![0, 1, 1, 1, 1, 1] =
        ![0, 1, 1, 2, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h4 (CartanMatrix.E 6) hM 3
  have h6 : IsRoot P a ![0, 1, 1, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 6) 4 ![0, 1, 1, 2, 1, 1] =
        ![0, 1, 1, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h5 (CartanMatrix.E 6) hM 4
  have h7 : IsRoot P a ![1, 1, 1, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 6) 0 ![0, 1, 1, 2, 2, 1] =
        ![1, 1, 1, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h6 (CartanMatrix.E 6) hM 0
  have h8 : IsRoot P a ![1, 1, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 6) 2 ![1, 1, 1, 2, 2, 1] =
        ![1, 1, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h7 (CartanMatrix.E 6) hM 2
  have h9 : IsRoot P a ![1, 1, 2, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 6) 3 ![1, 1, 2, 2, 2, 1] =
        ![1, 1, 2, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h8 (CartanMatrix.E 6) hM 3
  have h10 : IsRoot P a ![1, 2, 2, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 6) 1 ![1, 1, 2, 3, 2, 1] =
        ![1, 2, 2, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h9 (CartanMatrix.E 6) hM 1
  exact h10

end Langlands.CartanE6Root
