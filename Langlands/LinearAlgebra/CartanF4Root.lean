import Langlands.LinearAlgebra.RootReflectionCoefficients
import Mathlib.Data.Fintype.Pi

/-! # Cartan rigidity and an actual root with the F4 highest-root coefficients -/

noncomputable section

namespace Langlands.CartanF4Root

open RootReflectionCoefficients

/-- The oriented F4 Cartan matrix admits no nonidentity entry-preserving map. -/
theorem rigid (f : Fin 4 → Fin 4)
    (hf : ∀ i j, CartanMatrix.F₄ (f i) (f j) = CartanMatrix.F₄ i j) :
    ∀ i, f i = i := by
  have hd : ∀ i j : Fin 4, CartanMatrix.F₄ i j = -2 → i = 1 ∧ j = 2 := by
    simp only [CartanMatrix.F₄, Matrix.of_apply]
    decide
  have h12 : f 1 = 1 ∧ f 2 = 2 := hd _ _ (hf 1 2)
  have h0 : f 0 = 0 := by
    have h := hf 0 1
    have h' := hf 0 2
    rw [h12.1] at h
    rw [h12.2] at h'
    revert h h'
    generalize f 0 = x
    revert x
    simp only [CartanMatrix.F₄, Matrix.of_apply]
    decide
  have h3 : f 3 = 3 := by
    have h := hf 3 1
    have h' := hf 3 2
    rw [h12.1] at h
    rw [h12.2] at h'
    revert h h'
    generalize f 3 = x
    revert x
    simp only [CartanMatrix.F₄, Matrix.of_apply]
    decide
  intro i
  fin_cases i
  · exact h0
  · exact h12.1
  · exact h12.2
  · exact h3

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (a : Fin 4 → J)

/-- Seven actual reflections construct a root with integral coefficients
`(2, 3, 4, 2)` in every family with the actual F4 Cartan pairings. -/
theorem isRoot_highest
    (hM : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.F₄ i j) :
    IsRoot P a ![2, 3, 4, 2] := by
  have h0 : IsRoot P a ![1, 0, 0, 0] := by
    convert isRoot_single P a (0 : Fin 4) using 1
    ext i
    fin_cases i <;> simp
  have h1 : IsRoot P a ![1, 1, 0, 0] := by
    have he : reflect CartanMatrix.F₄ 1 ![1, 0, 0, 0] = ![1, 1, 0, 0] := by decide
    exact he ▸ IsRoot.reflect P a h0 CartanMatrix.F₄ hM 1
  have h2 : IsRoot P a ![1, 1, 2, 0] := by
    have he : reflect CartanMatrix.F₄ 2 ![1, 1, 0, 0] = ![1, 1, 2, 0] := by decide
    exact he ▸ IsRoot.reflect P a h1 CartanMatrix.F₄ hM 2
  have h3 : IsRoot P a ![1, 2, 2, 0] := by
    have he : reflect CartanMatrix.F₄ 1 ![1, 1, 2, 0] = ![1, 2, 2, 0] := by decide
    exact he ▸ IsRoot.reflect P a h2 CartanMatrix.F₄ hM 1
  have h4 : IsRoot P a ![1, 2, 2, 2] := by
    have he : reflect CartanMatrix.F₄ 3 ![1, 2, 2, 0] = ![1, 2, 2, 2] := by decide
    exact he ▸ IsRoot.reflect P a h3 CartanMatrix.F₄ hM 3
  have h5 : IsRoot P a ![1, 2, 4, 2] := by
    have he : reflect CartanMatrix.F₄ 2 ![1, 2, 2, 2] = ![1, 2, 4, 2] := by decide
    exact he ▸ IsRoot.reflect P a h4 CartanMatrix.F₄ hM 2
  have h6 : IsRoot P a ![1, 3, 4, 2] := by
    have he : reflect CartanMatrix.F₄ 1 ![1, 2, 4, 2] = ![1, 3, 4, 2] := by decide
    exact he ▸ IsRoot.reflect P a h5 CartanMatrix.F₄ hM 1
  have he : reflect CartanMatrix.F₄ 0 ![1, 3, 4, 2] = ![2, 3, 4, 2] := by decide
  exact he ▸ IsRoot.reflect P a h6 CartanMatrix.F₄ hM 0

end Langlands.CartanF4Root
