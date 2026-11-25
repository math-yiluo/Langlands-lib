/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Fixed field of automorphisms is purely inseparable

Source: Stacks Project, Fields, Lemma 030M (2).
(blueprint: lem-weil-pbc-normal-extension-fixed-field-purely-inseparable)
-/

@[expose] public section
universe u v

namespace Normal

/-- The fixed field in a normal extension is purely inseparable over the base.
Source: Stacks Project, Fields, Lemma 030M (2).
(blueprint: lem-weil-pbc-normal-extension-fixed-field-purely-inseparable)

Proof:
1. For a fixed element a, normality splits its minimal polynomial over E. Every root b
is the image of a under an F-automorphism (Stacks 0BME (2)), hence b=a because a is fixed.
Conversely a is a root by algebraicity. The finite set of distinct roots is therefore {a}.
2. Mathlib identifies the separable degree of a split polynomial with the number of
its distinct roots. Thus the minimal polynomial of a has separable degree one.
3. Minimal polynomials are unchanged by the injective inclusion of the fixed field in E.
The criterion isPurelyInseparable_iff_natSepDegree_eq_one now proves pure inseparability.
This works in characteristic zero and positive characteristic, for trivial extensions and
infinite normal extensions alike; only one algebraic element is considered at a time.
-/
theorem fixedField_purelyInseparable
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Normal F E] :
    IsPurelyInseparable F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) := by
  classical
  apply (isPurelyInseparable_iff_natSepDegree_eq_one F).2
  intro x
  have hm : minpoly F x = minpoly F (x : E) :=
    (minpoly.algHom_eq _ (IntermediateField.val _).injective x).symm
  rw [hm, Polynomial.natSepDegree_eq_of_splits _ (Normal.splits' (F := F) (x : E))]
  have hr : ((minpoly F (x : E)).aroots E).toFinset = {(x : E)} := by
    ext y
    simp only [Multiset.mem_toFinset, Finset.mem_singleton]
    constructor
    · intro hy
      obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
        (Algebra.IsAlgebraic.isAlgebraic (x : E)) (Polynomial.mem_aroots.mp hy).2
      exact hσ.symm.trans ((IntermediateField.mem_fixedField_iff _ _).mp x.property σ
        (Subgroup.mem_top σ))
    · rintro rfl
      exact Polynomial.mem_aroots.mpr
        ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral (x : E)), minpoly.aeval F (x : E)⟩
  rw [hr, Finset.card_singleton]

end Normal
