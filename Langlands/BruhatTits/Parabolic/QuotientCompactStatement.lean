import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Group.LeftQuotient
import Mathlib.NumberTheory.LocalField.Basic

/-! # Compactness target for actual dynamic-parabolic quotients -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits

/-- Both coset conventions for the actual rational points of a dynamic parabolic
have compact quotient topology over every nonarchimedean local field. -/
def DynamicParabolicQuotientCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    (hG : Langlands.GroupScheme.IsConnectedReductive G)
    (χ : (Langlands.GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let Gpts := (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    letI : TopologicalSpace Gpts :=
      Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X
    let P : Subgroup Gpts :=
      (Langlands.GroupScheme.Dynamic.parabolic χ).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))
    CompactSpace (Gpts ⧸ P) ∧ CompactSpace (Langlands.Induction.LeftQuotient P)

end Langlands.BruhatTits
