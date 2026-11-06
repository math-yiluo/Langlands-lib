import Langlands.Global.AdelicRestrictionSplitCentreQuotient
import Langlands.Global.AdelicReductiveFiniteVolumeStatement

/-! # Finite volume of the restriction split-centre quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
variable (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)

/-- The restriction quotient measure has the total mass of the norm-one quotient measure. -/
theorem quotientHaarMeasure_univ :
    quotientHaarMeasure F G S j Set.univ =
      AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G Set.univ := by
  rw [quotientHaarMeasure, Measure.map_apply (measurable_normOneToQuotient F G S j)
    MeasurableSet.univ, Set.preimage_univ]

/-- The restriction quotient measure is finite exactly when the norm-one quotient measure is. -/
theorem quotientHaarMeasure_isFiniteMeasure_iff :
    IsFiniteMeasure (quotientHaarMeasure F G S j) ↔
      IsFiniteMeasure (AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G) := by
  rw [isFiniteMeasure_iff, isFiniteMeasure_iff, quotientHaarMeasure_univ]

/-- Finite volume of `[G] = A_G G(F) \ G(𝔸_F)` (Getz–Hahn (2.21), Theorem 2.6.3 with (2.22)) for
connected reductive groups over number fields, with `A_G` given by a split component of the Weil
restriction. This proposition is a target and supplies no proof or measure instance. -/
def ConnectedReductiveQuotientFiniteVolumeStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
        (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G),
        IsSplitComponent j → IsFiniteMeasure (quotientHaarMeasure F G S j)

/-- Finite volume of the norm-one quotient for connected reductive groups gives finite volume of
the restriction split-centre quotient. -/
theorem connectedReductiveQuotientFiniteVolumeStatement_of_normOne
    (h : AdelicGroupPoints.ConnectedReductiveFiniteVolumeStatement.{0}) :
    ConnectedReductiveQuotientFiniteVolumeStatement :=
  fun F _ _ G _ _ hG S j _ =>
    (quotientHaarMeasure_isFiniteMeasure_iff F G S j).mpr (h F G hG)

end Langlands.Global.RestrictionSplitCentre
