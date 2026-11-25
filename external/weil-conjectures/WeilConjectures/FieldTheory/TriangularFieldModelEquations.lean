/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.List.OfFn

/-!
# Equations for a triangular field model

Source: Stacks Project, Algebra, proof of Tag 07BV, and the presentation in Tag 08JZ
(blueprint: def-weil-pbc-triangular-field-model-equations).
-/

@[expose] public section

universe u

namespace FieldTheory

/-- The equations `h T - 1, P₀, ..., Pᵣ₋₁` in `d + 1 + r` variables.
The first `d` variables are the transcendence variables, variable `d` is `T`, and
variable `d + 1 + i` is the new variable of `p i`. Its coefficients involve only
preceding variables. This is a real polynomial construction; no witnesses are chosen.
Source: Stacks Project, proof of Tags 07BV and 08JZ
(blueprint: def-weil-pbc-triangular-field-model-equations). -/
noncomputable def triangularFieldModelEquations
    (k : Type u) [CommRing k] (d r : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin r) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k)) :
    List (MvPolynomial (Fin (d + 1 + r)) k) :=
  (MvPolynomial.rename (fun j : Fin d =>
      (⟨j.val, by omega⟩ : Fin (d + 1 + r))) h *
      MvPolynomial.X ⟨d, by omega⟩ - 1) ::
    List.ofFn (fun i : Fin r =>
      Polynomial.eval₂
        (MvPolynomial.rename (fun j : Fin (d + 1 + i.val) =>
          (⟨j.val, by omega⟩ : Fin (d + 1 + r)))).toRingHom
        (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩) (p i))

/-- The localization equation contributes one entry and each tower generator one entry.
Source: Stacks Project, proof of Tag 07BV
(blueprint: def-weil-pbc-triangular-field-model-equations). -/
@[simp] theorem triangularFieldModelEquations_length
    (k : Type u) [CommRing k] (d r : ℕ) (h : MvPolynomial (Fin d) k)
    (p : (i : Fin r) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k)) :
    (triangularFieldModelEquations k d r h p).length = r + 1 := by
  simp [triangularFieldModelEquations]

end FieldTheory
