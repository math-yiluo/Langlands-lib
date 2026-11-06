import Langlands.LocalField.AlgebraicExtensionValuation
import Mathlib.RingTheory.Norm.Transitivity

/-! # Norm calibration and value bounds for a finite Galois extension -/

noncomputable section

universe u v

namespace Langlands.LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : Type v) [Field L] [Algebra F L]

section Algebraic

variable [Algebra.IsAlgebraic F L]

/-- Every base integer order occurs in the actual extension valuation. -/
theorem algebraicExtensionAddValuation_exists_integer_value (n : ℤ) :
    ∃ x : L, x ≠ 0 ∧ algebraicExtensionAddValuation F L x = ((n : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx, hn⟩ := FML.ord_surjective_nonzero F n
  exact ⟨algebraMap F L x, (map_ne_zero _).mpr hx,
    algebraicExtensionAddValuation_base_of_ord_eq F L hn⟩

end Algebraic

variable [FiniteDimensional F L]

/-- The integer order of the actual field norm, restricted to units. -/
def normOrderUnits : Lˣ →* Multiplicative ℤ :=
  (Plancherel.fieldOrderUnits F).comp (Units.map (Algebra.norm F))

variable [IsGalois F L]

/-- Applying the extension valuation to a norm multiplies the value by the degree. -/
theorem algebraicExtensionAddValuation_norm (x : L) :
    algebraicExtensionAddValuation F L (algebraMap F L (Algebra.norm F x)) =
      Module.finrank F L • algebraicExtensionAddValuation F L x := by
  classical
  let ν := algebraicExtensionAddValuation F L
  have hprod (s : Finset (L ≃ₐ[F] L)) :
      ν (∏ σ ∈ s, σ x) = s.card • ν x := by
    induction s using Finset.induction_on with
    | empty => simp [ν]
    | @insert σ s hσ ih =>
        rw [Finset.prod_insert hσ, AddValuation.map_mul,
          algebraicExtensionAddValuation_invariant F L, ih, Finset.card_insert_of_notMem hσ]
        simp [add_nsmul, add_comm, ν]
  rw [Algebra.norm_eq_prod_automorphisms]
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank] using hprod Finset.univ

/-- The integer norm order is exactly the degree times the finite extension value. -/
theorem normOrderUnits_eq_degree_value (a : Lˣ) :
    (((normOrderUnits F L a).toAdd : ℝ) : WithTop ℝ) =
      Module.finrank F L • algebraicExtensionAddValuation F L (a : L) := by
  rw [← algebraicExtensionAddValuation_norm F L]
  simpa only [normOrderUnits, MonoidHom.comp_apply, Units.coe_map] using
    (algebraicExtensionAddValuation_base_unit F L (Units.map (Algebra.norm F) a)).symm

/-- A nonzero element's value is the norm's integer order divided by the degree. -/
theorem algebraicExtensionAddValuation_unit_eq (a : Lˣ) :
    algebraicExtensionAddValuation F L (a : L) =
      (((normOrderUnits F L a).toAdd : ℝ) / Module.finrank F L : ℝ) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    ((algebraicExtensionAddValuation F L).ne_top_iff.mpr a.ne_zero)
  have hn := normOrderUnits_eq_degree_value F L a
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at hn
  rw [← hr]
  congr 1
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := F) (M := L))))).mpr
    (by simpa only [mul_comm] using hn.symm)

/-- The finite values lie in the lattice `(1 / [L:F]) * ℤ`. -/
theorem algebraicExtensionAddValuation_exists_lattice_value {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, algebraicExtensionAddValuation F L x =
      ((n : ℝ) / Module.finrank F L : ℝ) := by
  exact ⟨(normOrderUnits F L (Units.mk0 x hx)).toAdd,
    algebraicExtensionAddValuation_unit_eq F L (Units.mk0 x hx)⟩

end Langlands.LocalField
