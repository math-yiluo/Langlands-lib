import Langlands.BruhatTits.Unipotent.CompactOpenContainmentStatement
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

/-! # Jacquet compact-subgroup containment in actual dynamic unipotent radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits

/-- Compact-open containment in every actual dynamic unipotent radical implies
that each such radical, with the inherited canonical rational-point topology,
satisfies the Jacquet compact-subgroup containment predicate. -/
def DynamicUnipotentIsLimitOfCompactSubgroupsStatement : Prop :=
  DynamicUnipotentCompactOpenContainmentStatement.{u} →
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
      (hG : Langlands.GroupScheme.IsConnectedReductive G)
      (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace
          (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :=
        Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X
      Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups
        ((Langlands.GroupScheme.Dynamic.unipotent χ).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F)))))

end Langlands.BruhatTits
