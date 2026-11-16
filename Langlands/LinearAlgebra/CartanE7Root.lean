import Langlands.LinearAlgebra.CartanENumbering
import Langlands.LinearAlgebra.RootReflectionCoefficients

/-! # E7 rigidity and an actual root certificate -/

noncomputable section

namespace Langlands.CartanE7Root

open RootReflectionCoefficients CartanWalkColor

/-- The coefficient vector used in the E7 root certificate. -/
def coefficients : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]

/-- Five adjacency walk refinements distinguish all seven vertices. -/
theorem rigid (f : Fin 7 → Fin 7)
    (hf : ∀ i j, CartanMatrix.E 7 (f i) (f j) = CartanMatrix.E 7 i j) :
    ∀ i, f i = i := by
  have hbij : Function.Bijective f :=
    (Finite.injective_iff_bijective).mp (CartanENumbering.injective_of_preserves f hf)
  have h1 : step (CartanMatrix.E 7) (fun _ => 1) =
      ![1, 1, 2, 3, 2, 2, 1] := by decide
  have h2 : step (CartanMatrix.E 7) ![1, 1, 2, 3, 2, 2, 1] =
      ![2, 3, 4, 5, 5, 3, 2] := by decide
  have h3 : step (CartanMatrix.E 7) ![2, 3, 4, 5, 5, 3, 2] =
      ![4, 5, 7, 12, 8, 7, 3] := by decide
  have h4 : step (CartanMatrix.E 7) ![4, 5, 7, 12, 8, 7, 3] =
      ![7, 12, 16, 20, 19, 11, 7] := by decide
  have h5 : step (CartanMatrix.E 7) ![7, 12, 16, 20, 19, 11, 7] =
      ![16, 20, 27, 47, 31, 26, 11] := by decide
  have hi1 := step_invariant hf hbij (c := fun _ => 1) (fun _ => rfl)
  rw [h1] at hi1
  have hi2 := step_invariant hf hbij hi1
  rw [h2] at hi2
  have hi3 := step_invariant hf hbij hi2
  rw [h3] at hi3
  have hi4 := step_invariant hf hbij hi3
  rw [h4] at hi4
  have hi5 := step_invariant hf hbij hi4
  rw [h5] at hi5
  have hinj : Function.Injective (![16, 20, 27, 47, 31, 26, 11] : Fin 7 → ℕ) := by
    decide
  intro i
  exact hinj (hi5 i)

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (a : Fin 7 → J)

/-- Sixteen actual reflections construct a root with the selected E7
coefficient vector. -/
theorem isRoot_highest
    (hM : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.E 7 i j) :
    IsRoot P a coefficients := by
  have h0 : IsRoot P a ![0, 0, 0, 0, 0, 0, 1] := by
    convert isRoot_single P a (6 : Fin 7) using 1
    ext i
    fin_cases i <;> simp
  have h1 : IsRoot P a ![0, 0, 0, 0, 0, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 5 ![0, 0, 0, 0, 0, 0, 1] =
        ![0, 0, 0, 0, 0, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h0 (CartanMatrix.E 7) hM 5
  have h2 : IsRoot P a ![0, 0, 0, 0, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 4 ![0, 0, 0, 0, 0, 1, 1] =
        ![0, 0, 0, 0, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h1 (CartanMatrix.E 7) hM 4
  have h3 : IsRoot P a ![0, 0, 0, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 3 ![0, 0, 0, 0, 1, 1, 1] =
        ![0, 0, 0, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h2 (CartanMatrix.E 7) hM 3
  have h4 : IsRoot P a ![0, 0, 1, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 2 ![0, 0, 0, 1, 1, 1, 1] =
        ![0, 0, 1, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h3 (CartanMatrix.E 7) hM 2
  have h5 : IsRoot P a ![0, 1, 1, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 1 ![0, 0, 1, 1, 1, 1, 1] =
        ![0, 1, 1, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h4 (CartanMatrix.E 7) hM 1
  have h6 : IsRoot P a ![0, 1, 1, 2, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 3 ![0, 1, 1, 1, 1, 1, 1] =
        ![0, 1, 1, 2, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h5 (CartanMatrix.E 7) hM 3
  have h7 : IsRoot P a ![0, 1, 1, 2, 2, 1, 1] := by
    have he : reflect (CartanMatrix.E 7) 4 ![0, 1, 1, 2, 1, 1, 1] =
        ![0, 1, 1, 2, 2, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h6 (CartanMatrix.E 7) hM 4
  have h8 : IsRoot P a ![0, 1, 1, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 5 ![0, 1, 1, 2, 2, 1, 1] =
        ![0, 1, 1, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h7 (CartanMatrix.E 7) hM 5
  have h9 : IsRoot P a ![1, 1, 1, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 0 ![0, 1, 1, 2, 2, 2, 1] =
        ![1, 1, 1, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h8 (CartanMatrix.E 7) hM 0
  have h10 : IsRoot P a ![1, 1, 2, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 2 ![1, 1, 1, 2, 2, 2, 1] =
        ![1, 1, 2, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h9 (CartanMatrix.E 7) hM 2
  have h11 : IsRoot P a ![1, 1, 2, 3, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 3 ![1, 1, 2, 2, 2, 2, 1] =
        ![1, 1, 2, 3, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h10 (CartanMatrix.E 7) hM 3
  have h12 : IsRoot P a ![1, 1, 2, 3, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 4 ![1, 1, 2, 3, 2, 2, 1] =
        ![1, 1, 2, 3, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h11 (CartanMatrix.E 7) hM 4
  have h13 : IsRoot P a ![1, 2, 2, 3, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 1 ![1, 1, 2, 3, 3, 2, 1] =
        ![1, 2, 2, 3, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h12 (CartanMatrix.E 7) hM 1
  have h14 : IsRoot P a ![1, 2, 2, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 3 ![1, 2, 2, 3, 3, 2, 1] =
        ![1, 2, 2, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h13 (CartanMatrix.E 7) hM 3
  have h15 : IsRoot P a ![1, 2, 3, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 2 ![1, 2, 2, 4, 3, 2, 1] =
        ![1, 2, 3, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h14 (CartanMatrix.E 7) hM 2
  have h16 : IsRoot P a ![2, 2, 3, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 7) 0 ![1, 2, 3, 4, 3, 2, 1] =
        ![2, 2, 3, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h15 (CartanMatrix.E 7) hM 0
  exact h16

end Langlands.CartanE7Root
