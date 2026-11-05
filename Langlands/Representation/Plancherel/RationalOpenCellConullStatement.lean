import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Haar conullness of the actual rational dynamic open cell -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open HarishChandraSchwartz

/-- A geometric-measure prerequisite for the source open-cell formula.
This proposition is a proof target, not a structural instance or a theorem.
The actual open-cell embedding is already proved separately. -/
def RationalDynamicOpenCellConullStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    letI : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
    ∀ (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
      (mu : Measure (RationalPoint F G.X)), mu.IsHaarMeasure →
      mu (Set.range (openCellMap
        (P := (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
        (V := (Dynamic.unipotent (CommGroupScheme.groupHom
          (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).carrier
            (Over.mk (𝟙 (Spec (CommRingCat.of F)))))))ᶜ = 0

end Langlands.Plancherel
