import Langlands.Geometry.Building.TorusFiltration.Construction
import Langlands.Geometry.Building.TorusFiltration.StructuralStatements

/-! # Functoriality of the minimal congruent filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- Every homomorphism of tori preserves the minimal congruent filtration. -/
theorem minimalCongruentFunctoriality : MinimalCongruentFunctorialityStatement.{u} := by
  intro F _ _ _ _ T U _ _ hT hU f r
  have hCongruence (q : Set.Iio (1 : ℝ≥0)) (n : ℕ+) :
      (minimalCongruentShallowCongruence F T hT q n).map
          (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
        minimalCongruentShallowCongruence F U hU q n := by
    let M := minimalCongruentModel F T hT q
    let N := minimalCongruentModel F U hU q
    have hM := M.property.2.2.trans (minimalCongruentPoints_of_lt_one F T hT q)
    have hN := N.property.2.2.trans (minimalCongruentPoints_of_lt_one F U hU q)
    rw [minimalCongruentShallowCongruence_eq F T hT q n M.val M.property.1 hM,
      minimalCongruentShallowCongruence_eq F U hU q n N.val N.property.1 hN]
    obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F
      (M := N.val) (n := CommGroupScheme.groupHom f) M.property.1 rfl (by
        rw [hM, hN]
        exact map_minimalCongruentShallowSubgroup_le F T hT hU f q)
    rintro _ ⟨x, hx, rfl⟩
    exact φ.map_mem_congruenceSubgroupAt n hx
  unfold minimalCongruentPoints
  cases ⌊r⌋₊ with
  | zero => exact map_minimalCongruentShallowSubgroup_le F T hT hU f _
  | succ n => exact hCongruence _ (Nat.succPNat n)

end Langlands.Geometry.Building
