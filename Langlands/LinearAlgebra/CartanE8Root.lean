import Langlands.LinearAlgebra.RootReflectionCoefficients

/-! # An actual root with the E8 highest-root coefficients -/

noncomputable section

namespace Langlands.CartanE8Root

open RootReflectionCoefficients

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (a : Fin 8 → J)

/-- Twenty-eight actual reflections construct a root with integral
coefficients `(2, 3, 4, 6, 5, 4, 3, 2)` from the E8 Cartan pairings. -/
theorem isRoot_highest
    (hM : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.E 8 i j) :
    IsRoot P a ![2, 3, 4, 6, 5, 4, 3, 2] := by
  have h0 : IsRoot P a ![0, 0, 0, 0, 0, 0, 0, 1] := by
    convert isRoot_single P a (7 : Fin 8) using 1
    ext i
    fin_cases i <;> simp
  have h1 : IsRoot P a ![0, 0, 0, 0, 0, 0, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 6 ![0, 0, 0, 0, 0, 0, 0, 1] =
        ![0, 0, 0, 0, 0, 0, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h0 (CartanMatrix.E 8) hM 6
  have h2 : IsRoot P a ![0, 0, 0, 0, 0, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 5 ![0, 0, 0, 0, 0, 0, 1, 1] =
        ![0, 0, 0, 0, 0, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h1 (CartanMatrix.E 8) hM 5
  have h3 : IsRoot P a ![0, 0, 0, 0, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 4 ![0, 0, 0, 0, 0, 1, 1, 1] =
        ![0, 0, 0, 0, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h2 (CartanMatrix.E 8) hM 4
  have h4 : IsRoot P a ![0, 0, 0, 1, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 3 ![0, 0, 0, 0, 1, 1, 1, 1] =
        ![0, 0, 0, 1, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h3 (CartanMatrix.E 8) hM 3
  have h5 : IsRoot P a ![0, 0, 1, 1, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 2 ![0, 0, 0, 1, 1, 1, 1, 1] =
        ![0, 0, 1, 1, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h4 (CartanMatrix.E 8) hM 2
  have h6 : IsRoot P a ![0, 1, 1, 1, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 1 ![0, 0, 1, 1, 1, 1, 1, 1] =
        ![0, 1, 1, 1, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h5 (CartanMatrix.E 8) hM 1
  have h7 : IsRoot P a ![0, 1, 1, 2, 1, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 3 ![0, 1, 1, 1, 1, 1, 1, 1] =
        ![0, 1, 1, 2, 1, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h6 (CartanMatrix.E 8) hM 3
  have h8 : IsRoot P a ![0, 1, 1, 2, 2, 1, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 4 ![0, 1, 1, 2, 1, 1, 1, 1] =
        ![0, 1, 1, 2, 2, 1, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h7 (CartanMatrix.E 8) hM 4
  have h9 : IsRoot P a ![0, 1, 1, 2, 2, 2, 1, 1] := by
    have he : reflect (CartanMatrix.E 8) 5 ![0, 1, 1, 2, 2, 1, 1, 1] =
        ![0, 1, 1, 2, 2, 2, 1, 1] := by decide
    exact he ▸ IsRoot.reflect P a h8 (CartanMatrix.E 8) hM 5
  have h10 : IsRoot P a ![0, 1, 1, 2, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 6 ![0, 1, 1, 2, 2, 2, 1, 1] =
        ![0, 1, 1, 2, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h9 (CartanMatrix.E 8) hM 6
  have h11 : IsRoot P a ![1, 1, 1, 2, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 0 ![0, 1, 1, 2, 2, 2, 2, 1] =
        ![1, 1, 1, 2, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h10 (CartanMatrix.E 8) hM 0
  have h12 : IsRoot P a ![1, 1, 2, 2, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 2 ![1, 1, 1, 2, 2, 2, 2, 1] =
        ![1, 1, 2, 2, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h11 (CartanMatrix.E 8) hM 2
  have h13 : IsRoot P a ![1, 1, 2, 3, 2, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 3 ![1, 1, 2, 2, 2, 2, 2, 1] =
        ![1, 1, 2, 3, 2, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h12 (CartanMatrix.E 8) hM 3
  have h14 : IsRoot P a ![1, 1, 2, 3, 3, 2, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 4 ![1, 1, 2, 3, 2, 2, 2, 1] =
        ![1, 1, 2, 3, 3, 2, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h13 (CartanMatrix.E 8) hM 4
  have h15 : IsRoot P a ![1, 1, 2, 3, 3, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 5 ![1, 1, 2, 3, 3, 2, 2, 1] =
        ![1, 1, 2, 3, 3, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h14 (CartanMatrix.E 8) hM 5
  have h16 : IsRoot P a ![1, 2, 2, 3, 3, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 1 ![1, 1, 2, 3, 3, 3, 2, 1] =
        ![1, 2, 2, 3, 3, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h15 (CartanMatrix.E 8) hM 1
  have h17 : IsRoot P a ![1, 2, 2, 4, 3, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 3 ![1, 2, 2, 3, 3, 3, 2, 1] =
        ![1, 2, 2, 4, 3, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h16 (CartanMatrix.E 8) hM 3
  have h18 : IsRoot P a ![1, 2, 2, 4, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 4 ![1, 2, 2, 4, 3, 3, 2, 1] =
        ![1, 2, 2, 4, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h17 (CartanMatrix.E 8) hM 4
  have h19 : IsRoot P a ![1, 2, 3, 4, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 2 ![1, 2, 2, 4, 4, 3, 2, 1] =
        ![1, 2, 3, 4, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h18 (CartanMatrix.E 8) hM 2
  have h20 : IsRoot P a ![1, 2, 3, 5, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 3 ![1, 2, 3, 4, 4, 3, 2, 1] =
        ![1, 2, 3, 5, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h19 (CartanMatrix.E 8) hM 3
  have h21 : IsRoot P a ![2, 2, 3, 5, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 0 ![1, 2, 3, 5, 4, 3, 2, 1] =
        ![2, 2, 3, 5, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h20 (CartanMatrix.E 8) hM 0
  have h22 : IsRoot P a ![2, 2, 4, 5, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 2 ![2, 2, 3, 5, 4, 3, 2, 1] =
        ![2, 2, 4, 5, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h21 (CartanMatrix.E 8) hM 2
  have h23 : IsRoot P a ![2, 3, 4, 5, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 1 ![2, 2, 4, 5, 4, 3, 2, 1] =
        ![2, 3, 4, 5, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h22 (CartanMatrix.E 8) hM 1
  have h24 : IsRoot P a ![2, 3, 4, 6, 4, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 3 ![2, 3, 4, 5, 4, 3, 2, 1] =
        ![2, 3, 4, 6, 4, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h23 (CartanMatrix.E 8) hM 3
  have h25 : IsRoot P a ![2, 3, 4, 6, 5, 3, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 4 ![2, 3, 4, 6, 4, 3, 2, 1] =
        ![2, 3, 4, 6, 5, 3, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h24 (CartanMatrix.E 8) hM 4
  have h26 : IsRoot P a ![2, 3, 4, 6, 5, 4, 2, 1] := by
    have he : reflect (CartanMatrix.E 8) 5 ![2, 3, 4, 6, 5, 3, 2, 1] =
        ![2, 3, 4, 6, 5, 4, 2, 1] := by decide
    exact he ▸ IsRoot.reflect P a h25 (CartanMatrix.E 8) hM 5
  have h27 : IsRoot P a ![2, 3, 4, 6, 5, 4, 3, 1] := by
    have he : reflect (CartanMatrix.E 8) 6 ![2, 3, 4, 6, 5, 4, 2, 1] =
        ![2, 3, 4, 6, 5, 4, 3, 1] := by decide
    exact he ▸ IsRoot.reflect P a h26 (CartanMatrix.E 8) hM 6
  have h28 : IsRoot P a ![2, 3, 4, 6, 5, 4, 3, 2] := by
    have he : reflect (CartanMatrix.E 8) 7 ![2, 3, 4, 6, 5, 4, 3, 1] =
        ![2, 3, 4, 6, 5, 4, 3, 2] := by decide
    exact he ▸ IsRoot.reflect P a h27 (CartanMatrix.E 8) hM 7
  exact h28

end Langlands.CartanE8Root
