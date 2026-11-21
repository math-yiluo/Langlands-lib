import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction

/-! # Reindexing a comparison of standard epsilon exponents -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.BaseChange

open RankinSelberg
open scoped BigOperators

/-- A product comparison up to a constant unit depends only on the exponents
and the residue bases, and survives a bijective reindexing of the finite family. -/
def EpsilonComparisonReindexStatement : Prop :=
  ∀ (I : Type u) [Fintype I] (J : Type v) (X : Finset J) (e : I ≃ ↥X)
    (qF qE : ℕ) (aF : I → ℂˣ × ℤ) (aE : ℂˣ × ℤ)
    (bF : J → ℂˣ × ℤ) (bE : ℂˣ × ℤ),
    (∀ i, (aF i).2 = (bF (e i)).2) → aE.2 = bE.2 →
    EpsilonMonomialProductComparison qF qE Finset.univ aF aE →
      EpsilonMonomialProductComparison qF qE X bF bE

theorem epsilonComparisonReindex : EpsilonComparisonReindexStatement.{u, v} := by
  classical
  intro I _ J X e qF qE aF aE bF bE hF hE h
  obtain ⟨c, hc⟩ := h
  let a : ℂˣ := ∏ i, (aF i).1
  let b : ℂˣ := ∏ j ∈ X, (bF j).1
  refine ⟨b * c * aE.1 / (a * bE.1), fun z => ?_⟩
  have hx : (∏ j ∈ X, (spectralPoint qF z) ^ (bF j).2) =
      ∏ i, (spectralPoint qF z) ^ (aF i).2 := by
    rw [← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ fun i => congrArg (fun m : ℤ => spectralPoint qF z ^ m) (hF i)).symm
  have ha : (∏ i, ((aF i).1 : ℂ)) = (a : ℂ) :=
    (map_prod (Units.coeHom ℂ) _ _).symm
  have hb : (∏ j ∈ X, ((bF j).1 : ℂ)) = (b : ℂ) :=
    (map_prod (Units.coeHom ℂ) _ _).symm
  specialize hc z
  simp only [epsilonMonomial, Finset.prod_mul_distrib, ha, hE] at hc
  simp only [epsilonMonomial, Finset.prod_mul_distrib, hb, hx,
    Units.val_div_eq_div_val, Units.val_mul]
  field_simp [a.ne_zero, bE.1.ne_zero]
  linear_combination hc

end Langlands.BaseChange
