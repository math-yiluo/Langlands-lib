import Langlands.BruhatTits.Unipotent.JacquetCompactContainmentStatement

/-! # The S22 adapter to Jacquet compact-subgroup containment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits

/-- Forgetting openness in the S22 containment hypothesis gives the Jacquet
compact-subgroup containment property for each actual dynamic radical. -/
theorem dynamicUnipotent_isLimitOfCompactSubgroups :
    DynamicUnipotentIsLimitOfCompactSubgroupsStatement.{u} := by
  intro hS22 F _ _ _ _ G hG χ
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace
      (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X
  intro C hC
  obtain ⟨K, hK, hCK⟩ := hS22 F G hG χ C hC
  exact ⟨K.toSubgroup, hK, hCK⟩

end Langlands.BruhatTits
