import Langlands.FieldTheory.HenselianRealGaloisProlongationStatement
import Langlands.FieldTheory.HenselianFiniteGaloisInvariant
import Langlands.FieldTheory.FiniteGaloisValuationInvariance

/-! # Normalized Galois-invariant prolongation over a Henselian valuation ring -/

noncomputable section

universe u v

open scoped NNReal

namespace Langlands.FieldTheory

/-- A real valuation with Henselian valuation subring admits a normalized,
Galois-invariant prolongation to every algebraic Galois extension. -/
theorem henselianRealGaloisProlongation : HenselianRealGaloisProlongationStatement.{u,v} := by
  classical
  intro K _ ν hH Ω _ _ _
  let : HenselianLocalRing ν.valuationSubring := hH
  by_cases hn : ν.IsNontrivial
  · let w := realValuationProlongation (Ω := Ω) ν
    have hw : w.comap (algebraMap K Ω) = ν := realValuationProlongation_comap ν
    refine ⟨w, hw, ?_⟩
    apply valuation_invariant_of_finite_galois w
    intro F _ _ σ y
    have hF : (w.comap (algebraMap F Ω)).comap (algebraMap K F) = ν := by
      rw [← Valuation.comap_comp, ← IsScalarTower.algebraMap_eq, hw]
    exact realValuation_invariant_of_finiteGalois ν hn _ hF σ y
  · refine ⟨1, ?_, ?_⟩
    · apply Valuation.ext
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · rw [Valuation.comap_apply, Valuation.one_apply_of_ne_zero
          ((map_ne_zero_iff _ (algebraMap K Ω).injective).mpr hx)]
        by_contra h
        exact hn ⟨x, ν.ne_zero_iff.mpr hx, fun hx1 => h hx1.symm⟩
    · intro σ x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · rw [Valuation.one_apply_of_ne_zero ((map_ne_zero_iff _ σ.injective).mpr hx),
          Valuation.one_apply_of_ne_zero hx]

end Langlands.FieldTheory
