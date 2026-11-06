import Langlands.Representation.Plancherel.RationalOpenCellConullStatement

/-! # The algebraic boundary of the actual rational dynamic open cell -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open HarishChandraSchwartz

/-- The complement of the actual rational dynamic open cell is the
inverse image of a proper Zariski-closed subset of the actual group scheme. -/
def RationalDynamicOpenCellBoundaryStatement : Prop :=
  ∀ (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∀ (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G),
      ∃ Z : Set G.X.left, IsClosed Z ∧ Z ≠ Set.univ ∧
        (fun p : RationalPoint F G.X => p.left (IsLocalRing.closedPoint F)) ⁻¹' Z =
          (Set.range (openCellMap
            (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
            (V := (Dynamic.unipotent (CommGroupScheme.groupHom
              (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).carrier
                (Over.mk (𝟙 (Spec (CommRingCat.of F)))))))ᶜ

end Langlands.Plancherel
