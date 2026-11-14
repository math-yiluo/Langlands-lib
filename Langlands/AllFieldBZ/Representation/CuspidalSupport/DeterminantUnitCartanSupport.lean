import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnit
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport.LeviAdmissibility
open Langlands.CuspidalSupport.LeviAdmissibility hiding block_sums_eq_zero_of_determinantUnit_cartan
open Langlands.GeneralLinear
universe uF

variable {n : ℕ} (B : BlockShape n)

section Valuation
variable {K : Type uF} [Field K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

end Valuation
section Padic
variable {F : LocalFieldPackage.{uF}}

/-- The actual residue-normalized determinant-unit condition forces zero sums
in every block of a product Cartan factorization. -/
theorem block_sums_eq_zero_of_determinantUnit_cartan (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {ϖ : F.Carrierˣ},
      Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
      ∀ {g k₁ k₂ : B.Levi F.Carrier}
        {lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ},
        g ∈ determinantUnitSubgroup T B →
        k₁ ∈ integralLevi B → k₂ ∈ integralLevi B →
        g = k₁ * leviTorus B ϖ lam * k₂ →
        ∀ j, ∑ b, lam j b = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ϖ hϖ g k₁ k₂ lam hg hk₁ hk₂ hfact j
  apply sum_eq_zero_of_cartan (ValuativeRel.valuation F.Carrier) hϖ
    (congrFun hfact j) ((mem_integralLevi B).mp hk₁ j)
    ((mem_integralLevi B).mp hk₂ j)
  have hnorm := (mem_determinantUnitSubgroup_iff_normalizedAbs T B g).mp hg j
  rw [T.normalizedAbs_eq_one_iff_discreteValuation] at hnorm
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
    (ValuativeRel.valuation F.Carrier (GeneralLinear.determinant (g j) : F.Carrier)) = 1
      at hnorm
  apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).injective
  simpa using hnorm

end Padic
end Langlands.AllFieldBZ.CuspidalSupport.LeviAdmissibility
