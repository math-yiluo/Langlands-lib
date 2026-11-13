import Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
import Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit
import Langlands.AllField.Representation.Geometric.RefinementFunctors
import Langlands.AllField.Representation.Jacquet.Parabolic
noncomputable section

namespace Langlands.AllField.CuspidalSupport.LeviAdmissibility
open Langlands.CuspidalSupport.LeviAdmissibility hiding block_sums_eq_zero_of_determinantUnit_cartan
open Langlands.AllField.CuspidalSupport.LeviAdmissibility
open Langlands.CuspidalSupport hiding continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup isSmooth_determinantUnitRestriction leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF

variable {n : ℕ} (B : BlockShape n)

section Valuation

variable {K : Type uF} [Field K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

end Valuation

section Padic

variable {F : Type uF} [Field F]

/-- The actual residue-normalized determinant-unit condition forces zero sums
in every block of a product Cartan factorization. -/
theorem block_sums_eq_zero_of_determinantUnit_cartan (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {ϖ : Fˣ},
      Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      ∀ {g k₁ k₂ : B.Levi F}
        {lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ},
        g ∈ determinantUnitSubgroup T B →
        k₁ ∈ integralLevi B → k₂ ∈ integralLevi B →
        g = k₁ * leviTorus B ϖ lam * k₂ →
        ∀ j, ∑ b, lam j b = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ϖ hϖ g k₁ k₂ lam hg hk₁ hk₂ hfact j
  apply sum_eq_zero_of_cartan (ValuativeRel.valuation F) hϖ
    (congrFun hfact j) ((mem_integralLevi B).mp hk₁ j)
    ((mem_integralLevi B).mp hk₂ j)
  have hnorm := (mem_determinantUnitSubgroup_iff_normalizedAbs T B g).mp hg j
  rw [T.normalizedAbs_eq_one_iff_discreteValuation] at hnorm
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
    (ValuativeRel.valuation F (GeneralLinear.determinant (g j) : F)) = 1
      at hnorm
  apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective
  simpa using hnorm

end Padic

end Langlands.AllField.CuspidalSupport.LeviAdmissibility
